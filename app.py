"""My Cloud - multi-account Hugging Face storage pools + Telegram bot + web panel.

requirements.txt:
    fastapi uvicorn[standard] aiofiles httpx telethon cryptg huggingface_hub hf_transfer python-multipart cryptography

Storage model
    Every "pool" = one Hugging Face account token + one dataset repo (about 100 GB each).
    The first pool comes from the HF_TOKEN / HF_REPO secrets (the "primary" pool).
    More pools are added in the web panel (Storage page). They are saved encrypted in
    the primary dataset (.mycloud/pools.enc) so they survive Space restarts.
    New uploads go to the enabled pool with the most free space (or the one you pick).
"""
import os
import io
import re
import sys
import json
import time
import hmac
import uuid
import socket
import base64
import shutil
import asyncio
import hashlib
import logging
import secrets
import ipaddress
import mimetypes
import traceback
from contextlib import asynccontextmanager
from pathlib import Path, PurePosixPath
from urllib.parse import quote, unquote, urlsplit, urljoin

# Must be set BEFORE huggingface_hub is imported.
if os.getenv("STREAM_UPLOAD", "true").strip().lower() in {"1", "true", "yes", "on"}:
    os.environ.setdefault("HF_HUB_DISABLE_XET", "1")
os.environ.setdefault("HF_XET_HIGH_PERFORMANCE", "1")
try:
    import hf_transfer  # noqa: F401
    os.environ.setdefault("HF_HUB_ENABLE_HF_TRANSFER", "1")
except ImportError:
    pass

import aiofiles
import httpx
from fastapi import FastAPI, Request, Form, HTTPException
from fastapi.responses import HTMLResponse, RedirectResponse, JSONResponse
from huggingface_hub import HfApi
from huggingface_hub.utils import RepositoryNotFoundError
from telethon import TelegramClient, events
from telethon.sessions import MemorySession

logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s",
                    handlers=[logging.StreamHandler(sys.stdout)])
log = logging.getLogger("MyCloud")

# ───────────────────────── Config ─────────────────────────
def env_bool(name, default=False):
    return os.getenv(name, str(default)).strip().lower() in {"1", "true", "yes", "on"}

HF_TOKEN = os.environ.get("HF_TOKEN", "").strip()
HF_REPO = os.environ.get("HF_REPO", "").strip()
API_ID = int(os.environ.get("TG_API_ID", "0") or "0")
API_HASH = os.environ.get("TG_API_HASH", "").strip()
BOT_TOKEN = os.environ.get("TG_BOT_TOKEN", "").strip()
PUBLIC_BASE_URL = os.getenv("PUBLIC_BASE_URL", "").strip().rstrip("/")
ADMIN_USERNAME = os.getenv("ADMIN_USERNAME", "").strip()
ADMIN_PASSWORD = os.getenv("ADMIN_PASSWORD", "").strip()
ADMIN_PASSWORD_HASH = os.getenv("ADMIN_PASSWORD_HASH", "").strip()
SESSION_MAX_AGE = int(os.getenv("SESSION_MAX_AGE", "86400"))
COOKIE_NAME = os.getenv("COOKIE_NAME", "mc_session")
PROTECT_DOWNLOADS = env_bool("PROTECT_DOWNLOADS", False)
DEBUG_ERRORS = env_bool("DEBUG_ERRORS", False)
STREAM_UPLOAD = env_bool("STREAM_UPLOAD", True)
MAX_FILE_SIZE = int(os.getenv("MAX_FILE_SIZE", str(20 * 1024**3)))
MAX_FAILED = int(os.getenv("MAX_FAILED_ATTEMPTS", "5"))
LOCK_SECONDS = int(os.getenv("LOCK_SECONDS", "300"))
DEFAULT_LIMIT_GB = float(os.getenv("POOL_LIMIT_GB", "95"))  # headroom under HF's ~100 GB
VIDEO_EXT = {".mp4", ".webm", ".mov", ".m4v", ".mkv", ".ogv"}

SESSION_SECRET = (os.getenv("SESSION_SECRET", "").strip() or
                  hashlib.sha256(f"{HF_TOKEN}|{BOT_TOKEN}|{HF_REPO}|{ADMIN_USERNAME}".encode()).hexdigest()).encode()

SCRYPT_MAXMEM = 64 * 1024 * 1024

def b64e(d: bytes) -> str:
    return base64.urlsafe_b64encode(d).decode().rstrip("=")

def b64d(s: str) -> bytes:
    return base64.urlsafe_b64decode((s + "=" * (-len(s) % 4)).encode())

def hash_password(pw: str) -> str:
    salt = os.urandom(16)
    dk = hashlib.scrypt(pw.encode(), salt=salt, n=16384, r=8, p=1, dklen=32, maxmem=SCRYPT_MAXMEM)
    return f"scrypt$16384$8$1${b64e(salt)}${b64e(dk)}"

def verify_password(pw: str, encoded: str) -> bool:
    try:
        if not pw or not encoded:
            return False
        norm = encoded.strip()
        if norm.startswith("scrypt:"):
            norm = "scrypt$" + norm[7:].replace(":", "$", 3)
        parts = norm.split("$")
        if len(parts) != 6 or parts[0] != "scrypt":
            raise ValueError("bad hash format")
        _, n, r, p, salt, expected = parts
        expected = b64d(expected)
        dk = hashlib.scrypt(pw.encode(), salt=b64d(salt), n=int(n), r=int(r), p=int(p),
                            dklen=len(expected), maxmem=SCRYPT_MAXMEM)
        return hmac.compare_digest(dk, expected)
    except Exception:
        return bool(ADMIN_PASSWORD) and hmac.compare_digest(pw.encode(), ADMIN_PASSWORD.encode())

PASSWORD_HASH = ADMIN_PASSWORD_HASH or (hash_password(ADMIN_PASSWORD) if ADMIN_PASSWORD else "")
AUTH_ENABLED = bool(ADMIN_USERNAME and PASSWORD_HASH)
if not AUTH_ENABLED:
    log.warning("Auth disabled: set ADMIN_USERNAME and ADMIN_PASSWORD(_HASH). Anyone can upload!")

# ───────────────────────── Temp storage ─────────────────────────
_TMP_CANDIDATES = [Path(p) for p in (os.getenv("TMP_DIR", ""), "/dev/shm/mycloud", "/tmp/mycloud") if p]

def pick_tmp(size: int = 0) -> Path:
    """RAM disk if the file fits (fast), otherwise real disk."""
    need = int(size * 1.1) + 128 * 1024 * 1024
    for base in _TMP_CANDIDATES:
        try:
            base.mkdir(parents=True, exist_ok=True)
            if shutil.disk_usage(base).free > need:
                return base
        except Exception:
            continue
    Path("/tmp/mycloud").mkdir(parents=True, exist_ok=True)
    return Path("/tmp/mycloud")

# ───────────────────────── Sessions ─────────────────────────
def create_session_token(username: str) -> str:
    now = int(time.time())
    body = b64e(json.dumps({"sub": username, "iat": now, "exp": now + SESSION_MAX_AGE,
                            "jti": secrets.token_hex(8)}, separators=(",", ":")).encode())
    sig = b64e(hmac.new(SESSION_SECRET, body.encode(), hashlib.sha256).digest())
    return f"{body}.{sig}"

def get_current_user(request: Request):
    try:
        token = request.cookies.get(COOKIE_NAME) or ""
        body, sig = token.split(".", 1)
        good = b64e(hmac.new(SESSION_SECRET, body.encode(), hashlib.sha256).digest())
        if not hmac.compare_digest(sig, good):
            return None
        payload = json.loads(b64d(body))
        if int(payload.get("exp", 0)) < time.time():
            return None
        return payload.get("sub") or None
    except Exception:
        return None

def is_https(request: Request) -> bool:
    fwd = request.headers.get("x-forwarded-proto", "")
    if fwd:
        return fwd.split(",")[0].strip() == "https"
    return PUBLIC_BASE_URL.startswith("https://") or request.url.scheme == "https"

def safe_next(n) -> str:
    n = (n or "/").strip()
    return n if n.startswith("/") and not n.startswith("//") else "/"

def require_login(request: Request) -> str:
    if not AUTH_ENABLED:
        return "anonymous"
    user = get_current_user(request)
    if not user:
        raise HTTPException(401, "Login required")
    return user

def download_guard(request: Request):
    if PROTECT_DOWNLOADS and AUTH_ENABLED and not get_current_user(request):
        return RedirectResponse(f"/login?next={quote(request.url.path, safe='/')}", 302)

failed: dict = {}

# ───────────────────────── Storage pools ─────────────────────────
class Pool:
    """One Hugging Face account token + one dataset repo."""

    def __init__(self, id, token, repo, label="", limit_gb=DEFAULT_LIMIT_GB, enabled=True, source="ui", private=None):
        self.id, self.token, self.repo = id, token, repo
        self.label = label or repo.split("/")[-1]
        self.limit_gb, self.enabled, self.source, self.private = float(limit_gb), enabled, source, private
        self.api = HfApi(token=token)
        self.used, self.count, self.error = 0, 0, None

    @property
    def limit(self) -> int:
        return int(self.limit_gb * 1024**3)

    @property
    def free(self) -> int:
        return max(0, self.limit - self.used)

    def public(self) -> dict:
        t = self.token
        return {"id": self.id, "label": self.label, "repo": self.repo, "enabled": self.enabled,
                "limit_gb": self.limit_gb, "used": self.used, "free": self.free, "count": self.count,
                "error": self.error, "private": self.private, "source": self.source,
                "token_hint": (t[:4] + "…" + t[-4:]) if len(t) > 10 else "••••"}

    def stored(self) -> dict:
        return {"id": self.id, "label": self.label, "token": self.token, "repo": self.repo,
                "limit_gb": self.limit_gb, "enabled": self.enabled, "private": self.private}

POOLS: dict = {}
if HF_TOKEN and HF_REPO:
    POOLS["primary"] = Pool("primary", HF_TOKEN, HF_REPO, os.getenv("HF_LABEL", "Main"), DEFAULT_LIMIT_GB, source="env")

CFG_REPO_PATH = ".mycloud/pools.enc"
LOCAL_CFG = Path(os.getenv("DATA_DIR", "/tmp/mycloud_data")) / "pools.enc"

def _fernet():
    from cryptography.fernet import Fernet
    return Fernet(base64.urlsafe_b64encode(hashlib.sha256(SESSION_SECRET + b"|pools").digest()))

def _read_cfg_sync() -> list:
    blob, prim = None, POOLS.get("primary")
    if prim:
        try:
            from huggingface_hub import hf_hub_download
            blob = Path(hf_hub_download(repo_id=prim.repo, filename=CFG_REPO_PATH, repo_type="dataset",
                                        token=prim.token, force_download=True)).read_bytes()
        except Exception as e:
            log.info("No saved pools in primary dataset yet (%s)", type(e).__name__)
    if blob is None and LOCAL_CFG.exists():
        blob = LOCAL_CFG.read_bytes()
    if not blob:
        return []
    try:
        return json.loads(_fernet().decrypt(blob))
    except Exception as e:
        log.error("Could not read saved pools (wrong SESSION_SECRET or missing 'cryptography'?): %s", e)
        return []

def _save_cfg_sync():
    try:
        blob = _fernet().encrypt(json.dumps([p.stored() for p in POOLS.values() if p.source != "env"]).encode())
    except ImportError:
        raise RuntimeError("Install the 'cryptography' package so account tokens can be saved encrypted")
    try:
        LOCAL_CFG.parent.mkdir(parents=True, exist_ok=True)
        LOCAL_CFG.write_bytes(blob)
    except Exception as e:
        log.warning("Local pool config not written: %s", e)
    prim = POOLS.get("primary")
    if prim:
        prim.api.upload_file(path_or_fileobj=blob, path_in_repo=CFG_REPO_PATH, repo_id=prim.repo,
                             repo_type="dataset", commit_message="Update storage accounts")

async def load_pools():
    for d in await asyncio.to_thread(_read_cfg_sync):
        try:
            if d["id"] in POOLS or not d.get("token") or not d.get("repo"):
                continue
            POOLS[d["id"]] = Pool(d["id"], d["token"], d["repo"], d.get("label", ""),
                                  d.get("limit_gb", DEFAULT_LIMIT_GB), d.get("enabled", True), "ui", d.get("private"))
        except Exception as e:
            log.error("Skipped a saved pool: %s", e)
    log.info("Storage pools loaded: %d", len(POOLS))

# ───────────────────────── URL helpers ─────────────────────────
def safe_name(filename: str) -> str:
    name = Path((filename or "").replace("\\", "/")).name.strip()
    if not name or name in {".", ".."} or PurePosixPath(name).is_absolute():
        raise HTTPException(400, "Invalid filename")
    return name

def base_url(request=None) -> str:
    if PUBLIC_BASE_URL:
        return PUBLIC_BASE_URL
    if request is not None:
        proto = (request.headers.get("x-forwarded-proto") or request.url.scheme).split(",")[0].strip()
        host = (request.headers.get("x-forwarded-host") or request.headers.get("host") or "").split(",")[0].strip()
        if host:
            return f"{proto}://{host}"
    return ""

def hf_url(name: str, pool: Pool, download=False) -> str:
    return f"https://huggingface.co/datasets/{pool.repo}/resolve/main/{quote(safe_name(name))}" + ("?download=true" if download else "")

def links(name: str, request=None, pool: Pool = None) -> dict:
    b, q = base_url(request), quote(safe_name(name))
    if b or not pool:
        return {"download_url": f"{b}/download/{q}", "cdn_url": f"{b}/cdn/{q}"}
    return {"download_url": hf_url(name, pool, True), "cdn_url": hf_url(name, pool)}

# ───────────────────────── File index across pools ─────────────────────────
_cache = {"t": 0.0, "items": []}
_list_lock = asyncio.Lock()

def _list_pool_sync(p: Pool):
    out = []
    for e in p.api.list_repo_tree(repo_id=p.repo, repo_type="dataset", recursive=True):
        size = getattr(e, "size", None)
        if size is None or e.path.startswith(".") or e.path in {"README.md", ".gitattributes"}:
            continue
        out.append({"name": e.path, "size": size, "pool": p.id})
    return out

async def list_files(max_age: float = 5):
    async with _list_lock:
        if time.time() - _cache["t"] > max_age:
            pools = list(POOLS.values())
            res = await asyncio.gather(*[asyncio.to_thread(_list_pool_sync, p) for p in pools], return_exceptions=True)
            items, seen = [], set()
            for p, r in zip(pools, res):
                if isinstance(r, Exception):
                    p.error, p.used, p.count = (str(r) or type(r).__name__)[:200], 0, 0
                    continue
                p.error, p.used, p.count = None, sum(f["size"] for f in r), len(r)
                for f in r:
                    if f["name"] not in seen:
                        seen.add(f["name"])
                        items.append(f)
            items.sort(key=lambda x: x["name"].lower())
            _cache.update(items=items, t=time.time())
    return _cache["items"]

async def locate(name: str):
    """Which pool holds this file? Returns a Pool or None."""
    for age in (30, 5):
        f = next((f for f in await list_files(age) if f["name"] == name), None)
        if f:
            return POOLS.get(f["pool"])
    return None

async def choose_pool(size: int, name: str = None, preferred: str = None) -> Pool:
    """Replace in place if the file exists; else the chosen pool; else the pool with the most free space."""
    if not POOLS:
        raise ValueError("No storage account is connected yet. Add one on the Storage page.")
    items = await list_files(10)
    old = next((f for f in items if f["name"] == name), None) if name else None
    if old and old["pool"] in POOLS:
        return POOLS[old["pool"]]
    ok = [p for p in POOLS.values() if p.enabled and not p.error and p.free >= size]
    if preferred:
        pp = POOLS.get(preferred)
        if pp and pp in ok:
            return pp
        raise ValueError("The chosen account is paused, unreachable or out of space. Pick another or use Automatic.")
    if not ok:
        raise ValueError("No connected account has enough free space. Add another account on the Storage page.")
    return max(ok, key=lambda p: p.free)

async def pick(size, name=None, preferred=None) -> Pool:
    try:
        return await choose_pool(size, name, preferred or None)
    except ValueError as e:
        raise HTTPException(507, str(e))

async def push_to_hf(path, name: str, note: str, pool: Pool):
    await asyncio.to_thread(pool.api.upload_file, path_or_fileobj=str(path), path_in_repo=name,
                            repo_id=pool.repo, repo_type="dataset", commit_message=f"{note}: {name}")
    _cache["t"] = 0

# ───────────────────────── Jobs (URL import) ─────────────────────────
JOBS: dict = {}

def new_job(name: str) -> dict:
    now = time.time()
    for k in [k for k, j in JOBS.items() if now - j["ts"] > 3600 and j["stage"] in ("done", "error")]:
        JOBS.pop(k, None)
    job = {"id": uuid.uuid4().hex[:10], "name": name, "stage": "queued", "done": 0, "total": 0,
           "speed": 0, "error": None, "ts": now}
    JOBS[job["id"]] = job
    return job

async def assert_public(url: str):
    """SSRF guard: only public http(s) hosts."""
    u = urlsplit(url)
    if u.scheme not in ("http", "https") or not u.hostname:
        raise ValueError("Only http(s) links are supported")
    infos = await asyncio.get_running_loop().getaddrinfo(
        u.hostname, u.port or (443 if u.scheme == "https" else 80), type=socket.SOCK_STREAM)
    if any(not ipaddress.ip_address(i[4][0]).is_global for i in infos):
        raise ValueError("That address is private and can't be fetched")

def guess_name(resp, url: str) -> str:
    cd = resp.headers.get("content-disposition", "")
    m = re.search(r"filename\*?=(?:UTF-8'')?\"?([^\";]+)", cd, re.I)
    name = unquote(m.group(1)) if m else unquote(urlsplit(url).path.rsplit("/", 1)[-1])
    name = Path(name.replace("\\", "/")).name.strip() or f"file_{uuid.uuid4().hex[:8]}"
    if not Path(name).suffix:
        name += mimetypes.guess_extension((resp.headers.get("content-type") or "").split(";")[0].strip()) or ""
    return name

async def run_remote(job: dict, url: str, name: str, preferred: str = ""):
    tmp = None
    try:
        headers = {"User-Agent": "Mozilla/5.0 (MyCloud)"}
        async with httpx.AsyncClient(follow_redirects=False, headers=headers,
                                     timeout=httpx.Timeout(30, read=120)) as http:
            cur = url
            for _ in range(6):
                await assert_public(cur)
                resp = await http.send(http.build_request("GET", cur), stream=True)
                if resp.status_code in (301, 302, 303, 307, 308):
                    cur = urljoin(cur, resp.headers.get("location", ""))
                    await resp.aclose()
                    continue
                break
            else:
                raise ValueError("Too many redirects")
            try:
                if resp.status_code >= 400:
                    raise ValueError(f"The source answered HTTP {resp.status_code}")
                total = int(resp.headers.get("content-length") or 0)
                if total > MAX_FILE_SIZE:
                    raise ValueError("File is larger than the size limit")
                fname = safe_name(name) if name else guess_name(resp, cur)
                if name and not Path(fname).suffix:
                    fname += Path(guess_name(resp, cur)).suffix
                await choose_pool(total, fname, preferred or None)  # fail early if nothing fits
                job.update(name=fname, total=total, stage="downloading")
                tmp = pick_tmp(total) / f"{uuid.uuid4().hex}_{fname}"
                t0 = time.time()
                async with aiofiles.open(tmp, "wb") as out:
                    async for chunk in resp.aiter_bytes(1024 * 1024):
                        job["done"] += len(chunk)
                        if job["done"] > MAX_FILE_SIZE:
                            raise ValueError("File is larger than the size limit")
                        await out.write(chunk)
                        job["speed"] = job["done"] / max(time.time() - t0, 0.1)
            finally:
                await resp.aclose()
        job.update(stage="uploading", total=job["done"], speed=0)
        pool = await choose_pool(job["done"], fname, preferred or None)
        await push_to_hf(tmp, fname, "URL import", pool)
        job.update(stage="done", **links(fname, pool=pool))
        log.info("URL import OK: %s (%.1f MB) -> %s", fname, job["done"] / 1048576, pool.label)
    except Exception as e:
        log.error("URL import failed: %s", e)
        job.update(stage="error", error=str(e) or type(e).__name__)
    finally:
        if tmp:
            Path(tmp).unlink(missing_ok=True)

# ───────────────────────── Subtitles (mkvmerge / ffmpeg) ─────────────────────────
MUX_SEM = asyncio.Semaphore(1)

def _ext(name: str, default: str) -> str:
    e = Path(name).suffix.lower()
    return e if re.fullmatch(r"\.[a-z0-9]{1,5}", e) else default

def mkv_name(name: str) -> str:
    name = Path(name.replace("\\", "/")).name.strip() or "output"
    if name.lower().endswith(".mkv"):
        return name
    if Path(name).suffix.lower() in (VIDEO_EXT | {".avi"}):
        return str(Path(name).with_suffix(".mkv"))
    return name + ".mkv"

def mp4_name(name: str) -> str:
    name = Path(name.replace("\\", "/")).name.strip() or "output"
    if name.lower().endswith(".mp4"):
        return name
    if Path(name).suffix.lower() in (VIDEO_EXT | {".avi"}):
        return str(Path(name).with_suffix(".mp4"))
    return name + ".mp4"

async def fetch_source(job: dict, src: dict, dest_stem: Path, label: str, default_ext: str):
    """Download a storage file (from whichever pool holds it) or a public URL to disk."""
    if src["type"] == "storage":
        name = safe_name(src["value"])
        pool = await locate(name)
        if not pool:
            raise ValueError(f"{name} was not found in any connected account")
        url, public = hf_url(name, pool), False
        auth = {"Authorization": f"Bearer {pool.token}"}
    else:
        url, public, name, auth = src["value"], True, "", None
    async with httpx.AsyncClient(follow_redirects=False, headers={"User-Agent": "Mozilla/5.0 (MyCloud)"},
                                 timeout=httpx.Timeout(30, read=120)) as http:
        cur = url
        for hop in range(6):
            if public:
                await assert_public(cur)
            resp = await http.send(http.build_request("GET", cur, headers=auth if hop == 0 else None), stream=True)
            if resp.status_code in (301, 302, 303, 307, 308):
                cur = urljoin(cur, resp.headers.get("location", ""))
                await resp.aclose()
                continue
            break
        else:
            raise ValueError("Too many redirects")
        try:
            if resp.status_code >= 400:
                raise ValueError(f"The {label} source answered HTTP {resp.status_code}")
            name = name or guess_name(resp, cur)
            dest = dest_stem.with_suffix(_ext(name, default_ext))
            total, done = int(resp.headers.get("content-length") or 0), 0
            async with aiofiles.open(dest, "wb") as out:
                async for chunk in resp.aiter_bytes(1024 * 1024):
                    done += len(chunk)
                    if done > MAX_FILE_SIZE:
                        raise ValueError("File is larger than the size limit")
                    await out.write(chunk)
                    job.update(label=f"Downloading {label} · {done / 1048576:.0f} MB", pct=(done * 100 // total if total else None))
            return dest, name
        finally:
            await resp.aclose()

async def run_mux(job: dict, v: dict, sub: dict, out_name: str, lang: str, track: str):
    work = None
    try:
        if not shutil.which("mkvmerge"):
            raise ValueError("mkvmerge is not installed on the server (install the mkvtoolnix package)")
        job.update(stage="working", label="Waiting for another merge to finish", pct=None)
        async with MUX_SEM:
            size = next((f["size"] for f in _cache["items"] if v["type"] == "storage" and f["name"] == v["value"]), 0)
            work = pick_tmp((size or 2 * 1024**3) * 2) / f"mux_{job['id']}"
            work.mkdir(parents=True, exist_ok=True)
            vpath, vname = await fetch_source(job, v, work / "video", "video", ".mkv")
            spath, _ = await fetch_source(job, sub, work / "sub", "subtitle", ".srt")
            out_name = job["name"] = mkv_name(out_name or f"{Path(vname).stem}_sub.mkv")
            if v["type"] == "storage" and out_name == vname:
                raise ValueError("Choose a different output name so the original video isn't overwritten")
            out = work / "out.mkv"
            cmd = ["mkvmerge", "-o", str(out), str(vpath), "--language", f"0:{lang}", "--track-name", f"0:{track}"]
            if spath.suffix in {".srt", ".ass", ".ssa"}:
                cmd += ["--sub-charset", "0:UTF-8"]
            cmd.append(str(spath))
            job.update(label="Merging subtitles", pct=0)
            proc = await asyncio.create_subprocess_exec(*cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT)
            tail = b""
            while chunk := await proc.stdout.read(4096):
                tail = (tail + chunk)[-3000:]
                m = re.findall(rb"Progress: (\d+)%", tail)
                if m:
                    job["pct"] = int(m[-1])
            rc = await proc.wait()
            if rc >= 2 or not out.exists():
                msg = re.sub(r"Progress: \d+%\s*", "", tail.decode("utf-8", "replace")).strip()[-300:]
                raise ValueError("mkvmerge failed: " + msg)
            pool = await choose_pool(out.stat().st_size, out_name)
            job.update(label=f"Saving to {pool.label}…", pct=None)
            await push_to_hf(out, out_name, "Subtitle mux", pool)
        job.update(stage="done", label=None, **links(out_name, pool=pool))
        log.info("Subtitle mux OK: %s", out_name)
    except Exception as e:
        log.error("Subtitle mux failed: %s", e)
        job.update(stage="error", error=str(e) or type(e).__name__)
    finally:
        if work:
            shutil.rmtree(work, ignore_errors=True)

async def run_burn(job: dict, v: dict, sub: dict, out_name: str, font: str, size: int, crf: int, preset: str):
    """Hardcode (burn-in) subtitles with ffmpeg. Re-encodes the video, so it is CPU heavy."""
    work = None
    try:
        if not (shutil.which("ffmpeg") and shutil.which("ffprobe")):
            raise ValueError("ffmpeg is not installed on the server (add ffmpeg to the Dockerfile)")
        job.update(stage="working", label="Waiting for another job to finish", pct=None)
        async with MUX_SEM:
            hint = next((f["size"] for f in _cache["items"] if v["type"] == "storage" and f["name"] == v["value"]), 0)
            work = pick_tmp((hint or 2 * 1024**3) * 2) / f"burn_{job['id']}"
            work.mkdir(parents=True, exist_ok=True)
            vpath, vname = await fetch_source(job, v, work / "video", "video", ".mkv")
            spath, _ = await fetch_source(job, sub, work / "sub", "subtitle", ".srt")
            out_name = job["name"] = mp4_name(out_name or f"{Path(vname).stem}_hardsub.mp4")
            if v["type"] == "storage" and out_name == vname:
                raise ValueError("Choose a different output name so the original video isn't overwritten")
            probe = await asyncio.create_subprocess_exec(
                "ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", str(vpath),
                stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.DEVNULL)
            try:
                duration = float((await probe.communicate())[0].decode().strip() or 0)
            except ValueError:
                duration = 0.0
            vf = f"subtitles={spath.name}:force_style='FontName={font},FontSize={size},Outline=2,Shadow=0'"
            cmd = ["ffmpeg", "-y", "-nostdin", "-loglevel", "error", "-progress", "pipe:1", "-nostats",
                   "-i", str(vpath), "-map", "0:v:0", "-map", "0:a?", "-sn", "-vf", vf,
                   "-c:v", "libx264", "-preset", preset, "-crf", str(crf), "-pix_fmt", "yuv420p",
                   "-c:a", "aac", "-b:a", "192k", "-movflags", "+faststart", "out.mp4"]
            job.update(label="Encoding video", pct=0 if duration else None)
            proc = await asyncio.create_subprocess_exec(*cmd, cwd=str(work), stdout=asyncio.subprocess.PIPE,
                                                        stderr=asyncio.subprocess.STDOUT)
            tail = b""
            while chunk := await proc.stdout.read(4096):
                tail = (tail + chunk)[-3000:]
                m = re.findall(rb"out_time_(?:us|ms)=(\d+)", tail)
                if m and duration:
                    job.update(label="Encoding video", pct=min(99, int(int(m[-1]) / 1e6 * 100 / duration)))
            rc = await proc.wait()
            out = work / "out.mp4"
            if rc != 0 or not out.exists():
                msg = re.sub(rb"[a-z_0-9]+=\S*\s*", b"", tail).decode("utf-8", "replace").strip()[-300:]
                raise ValueError("ffmpeg failed: " + msg)
            pool = await choose_pool(out.stat().st_size, out_name)
            job.update(label=f"Saving to {pool.label}…", pct=None)
            await push_to_hf(out, out_name, "Hardsub", pool)
        job.update(stage="done", label=None, **links(out_name, pool=pool))
        log.info("Hardsub OK: %s", out_name)
    except Exception as e:
        log.error("Hardsub failed: %s", e)
        job.update(stage="error", error=str(e) or type(e).__name__)
    finally:
        if work:
            shutil.rmtree(work, ignore_errors=True)

# ───────────────────────── App ─────────────────────────
client = TelegramClient(MemorySession(), API_ID, API_HASH) if API_ID and API_HASH else None
tg_state = {"ok": False, "error": None}

async def start_telegram():
    try:
        await client.start(bot_token=BOT_TOKEN)
        tg_state["ok"] = True
        log.info("Telegram bot connected")
    except Exception as e:
        tg_state["error"] = str(e)
        log.error("Telegram startup failed: %s", e)

@asynccontextmanager
async def lifespan(app):
    await load_pools()
    if client:
        register_telegram()
        asyncio.create_task(start_telegram())
    yield
    if client:
        try:
            await client.disconnect()
        except Exception:
            pass

app = FastAPI(title="My Cloud", lifespan=lifespan)

@app.exception_handler(Exception)
async def on_error(request: Request, exc: Exception):
    eid = secrets.token_hex(6)
    log.error("Unhandled [%s]\n%s", eid, traceback.format_exc())
    data = {"detail": "Internal Server Error", "error_id": eid}
    if DEBUG_ERRORS:
        data["exception"] = f"{type(exc).__name__}: {exc}"
    return JSONResponse(data, status_code=500)

# ───────────────────────── Web UI ─────────────────────────
BASE_CSS = """
:root{--bg:#ECEFE9;--card:#FBFBF8;--ink:#16211C;--mute:#5E6B63;--line:#D3DACF;--acc:#17594A;--acc-ink:#fff;--ok:#12813f;--bad:#b3261e;--warn:#8a5a00;--field:#F3F5F0;--side:#10261F}
@media(prefers-color-scheme:dark){:root{--bg:#0C1210;--card:#141C18;--ink:#E6EEE9;--mute:#93A39A;--line:#25312B;--acc:#5FD3AE;--acc-ink:#07130E;--ok:#4cc37f;--bad:#ff8a80;--warn:#e3b04b;--field:#0F1613;--side:#08100D}}
*{box-sizing:border-box;margin:0}
[hidden]{display:none!important}
body{font-family:'Instrument Sans',system-ui,-apple-system,'Segoe UI',sans-serif;background:var(--bg);color:var(--ink);line-height:1.5;-webkit-font-smoothing:antialiased}
h1,h2,h3,.brand{font-family:'Bricolage Grotesque','Instrument Sans',system-ui,sans-serif}
button,input,textarea,select{font:inherit;color:inherit}
:focus-visible{outline:2px solid var(--acc);outline-offset:2px}
.btn{background:var(--acc);color:var(--acc-ink);border:0;border-radius:8px;padding:10px 16px;font-weight:600;cursor:pointer}
.btn:disabled{opacity:.5;cursor:default}
.btn.ghost{background:transparent;color:var(--ink);border:1px solid var(--line)}
.btn.ghost:hover{border-color:var(--mute)}
.btn.danger{color:var(--bad)}
.btn.sm{padding:6px 11px;font-size:.82rem;font-weight:500}
input[type=text],input[type=password],input[type=number],textarea,select{width:100%;background:var(--field);border:1px solid var(--line);border-radius:8px;padding:10px 12px}
"""

FONT = ('<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>'
        '<link href="https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:wght@600;800&family=Instrument+Sans:wght@400;500;600&display=swap" rel="stylesheet">')

LOGIN_HTML = """<!DOCTYPE html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Sign in · My Cloud</title>""" + FONT + "<style>" + BASE_CSS + """
body{min-height:100vh;display:grid;place-items:center;padding:20px}
form{width:100%;max-width:380px;background:var(--card);border:1px solid var(--line);border-radius:16px;padding:32px}
h1{font-size:1.9rem;font-weight:800;letter-spacing:-.03em;margin-bottom:4px}
p.s{color:var(--mute);margin-bottom:24px}label{display:block;font-size:.85rem;color:var(--mute);margin:14px 0 6px}
.btn{width:100%;margin-top:22px}.err{background:color-mix(in srgb,var(--bad) 12%,transparent);color:var(--bad);padding:10px 12px;border-radius:8px;margin-bottom:8px;font-size:.9rem}
</style></head><body><form method="post" action="/login"><h1>My Cloud</h1><p class="s">Sign in to manage your files and storage.</p>
%%ERROR%%<input type="hidden" name="next" value="%%NEXT%%">
<label for="u">Username</label><input id="u" name="username" type="text" autocomplete="username" required>
<label for="p">Password</label><input id="p" name="password" type="password" autocomplete="current-password" required>
<button class="btn" type="submit">Sign in</button></form></body></html>"""

DASH_CSS = r"""
.app{display:grid;grid-template-columns:232px minmax(0,1fr);min-height:100vh}
aside{background:var(--side);color:#E6EFEA;padding:26px 14px;position:sticky;top:0;height:100vh;display:flex;flex-direction:column;gap:4px}
.brand{font-weight:800;font-size:1.4rem;letter-spacing:-.03em;padding:0 12px 20px}
.nv{display:block;width:100%;text-align:left;background:none;border:0;color:#B3C5BB;padding:10px 12px;border-radius:8px;cursor:pointer;font-weight:500}
.nv:hover{color:#fff}.nv[aria-current=page]{background:rgba(255,255,255,.11);color:#fff}
.me{margin-top:auto;padding:0 12px;font-size:.85rem;color:#9DB0A6;display:flex;justify-content:space-between;align-items:center;gap:8px}
.me button{background:none;border:1px solid rgba(255,255,255,.22);color:#E6EFEA;border-radius:8px;padding:5px 10px;cursor:pointer;font-size:.8rem}
main{padding:clamp(20px,4vw,46px);max-width:1020px;width:100%}
h1{font-size:clamp(2rem,4.5vw,2.8rem);font-weight:800;letter-spacing:-.035em;line-height:1.05;margin-bottom:8px}
.lead{color:var(--mute);margin-bottom:24px;max-width:56ch}
.panel{background:var(--card);border:1px solid var(--line);border-radius:16px}
.pad{padding:22px}
.cap{display:flex;gap:4px;height:16px;margin:16px 0 14px}
.cap i{display:block;height:100%;background:var(--line);border-radius:5px;overflow:hidden;position:relative;min-width:6px}
.cap b{position:absolute;inset:0 auto 0 0;display:block;min-width:2px}
.leg{display:flex;flex-wrap:wrap;gap:6px 20px;font-size:.85rem}.leg em{color:var(--mute);font-style:normal}
.dot{display:inline-block;width:10px;height:10px;border-radius:3px;margin-right:7px;flex:none}
.cap-t{font-family:'Bricolage Grotesque',sans-serif;font-size:1.3rem;font-weight:600;letter-spacing:-.02em}
.tools{display:flex;gap:10px;margin:28px 0 12px;flex-wrap:wrap;align-items:center}.tools input{flex:1;min-width:180px}.tools select{width:auto;max-width:220px}
.tools .c{color:var(--mute);font-size:.9rem}
.f{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:8px 14px;padding:14px 18px;border-bottom:1px solid var(--line)}
.f:last-child{border:0}.f .n{font-weight:500;word-break:break-all}.f .sz{color:var(--mute);font-size:.85rem;font-variant-numeric:tabular-nums}
.f .m{display:flex;align-items:center;gap:6px;color:var(--mute);font-size:.8rem;margin-top:2px}
.f .a{grid-column:1/-1;display:flex;gap:6px;flex-wrap:wrap}
.empty{padding:36px;text-align:center;color:var(--mute)}
.two{display:grid;grid-template-columns:1fr 1fr;gap:16px;align-items:start}
.drop{display:block;border:2px dashed var(--line);border-radius:12px;padding:40px 18px;text-align:center;cursor:pointer;transition:border-color .15s,background .15s}
.drop:hover,.drop.over{border-color:var(--acc);background:color-mix(in srgb,var(--acc) 7%,transparent)}
.drop b{display:block;font-size:1.1rem;margin-bottom:4px}.drop span{color:var(--mute);font-size:.88rem}
h2{font-size:1.15rem;font-weight:600;letter-spacing:-.015em;margin-bottom:12px}
label.l{display:block;font-size:.82rem;color:var(--mute);margin:12px 0 5px}
textarea{min-height:110px;resize:vertical}
.hint{color:var(--mute);font-size:.85rem;margin-top:10px}
.seg{display:inline-flex;border:1px solid var(--line);border-radius:8px;overflow:hidden;margin-bottom:12px}
.seg button{background:none;border:0;padding:7px 14px;cursor:pointer;color:var(--mute);font-size:.86rem}
.seg button[aria-pressed=true]{background:var(--acc);color:var(--acc-ink)}
.src{border:1px solid var(--line);border-radius:12px;padding:14px;min-width:0;margin-bottom:14px}.src legend{padding:0 6px;font-weight:600;font-size:.9rem}
.pk{position:relative}
.pk-list{position:absolute;left:0;right:0;top:calc(100% + 4px);max-height:240px;overflow:auto;background:var(--card);border:1px solid var(--line);border-radius:10px;z-index:5;box-shadow:0 8px 24px rgba(0,0,0,.16)}
.pk-list div{padding:8px 12px;cursor:pointer;word-break:break-all;display:flex;justify-content:space-between;gap:10px;font-size:.9rem}
.pk-list div:hover{background:color-mix(in srgb,var(--acc) 10%,transparent)}.pk-list small{color:var(--mute);white-space:nowrap}.pk-list .none{color:var(--mute);cursor:default}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:12px}
.pools{display:grid;gap:14px;margin-top:16px}
.pool{padding:18px 20px}
.ph{display:flex;gap:12px;align-items:flex-start}.ph .dot{margin-top:7px;width:12px;height:12px}
.ph h3{font-size:1.05rem;font-weight:600}.ph a{color:var(--mute);font-size:.85rem;word-break:break-all}.ph>div{flex:1;min-width:0}
.badge{font-size:.78rem;padding:3px 10px;border-radius:99px;border:1px solid var(--line);color:var(--mute);white-space:nowrap}
.badge.on{color:var(--ok);border-color:color-mix(in srgb,var(--ok) 40%,transparent)}.badge.bad{color:var(--bad);border-color:color-mix(in srgb,var(--bad) 40%,transparent)}
.bar2{height:8px;background:var(--line);border-radius:4px;overflow:hidden;margin:14px 0 8px}.bar2 b{display:block;height:100%}
.meta{color:var(--mute);font-size:.85rem}.warn{font-size:.85rem;color:var(--warn);margin-top:8px}.warn.bad{color:var(--bad)}
.pool .a{display:flex;gap:6px;margin-top:14px;flex-wrap:wrap}
.perr{color:var(--bad);font-size:.9rem;margin-top:10px}
.chk{display:flex;gap:8px;align-items:center;margin-top:14px;font-size:.9rem}.chk input{width:auto}
dialog{border:0;border-radius:14px;padding:0;background:#000;max-width:min(92vw,960px);width:100%}dialog::backdrop{background:rgba(0,0,0,.7)}
dialog video{display:block;width:100%;max-height:80vh}dialog form{position:absolute;top:8px;right:8px}
#toast{position:fixed;bottom:20px;left:50%;transform:translateX(-50%);background:var(--ink);color:var(--bg);padding:10px 16px;border-radius:8px;font-size:.9rem;opacity:0;pointer-events:none;transition:opacity .2s;z-index:30}#toast.on{opacity:1}
#xfers{position:fixed;right:16px;bottom:16px;width:min(360px,calc(100vw - 32px));display:grid;gap:8px;z-index:20}
.x{border:1px solid var(--line);border-radius:12px;padding:12px 14px;background:var(--card);box-shadow:0 8px 24px rgba(0,0,0,.14)}
.x .top{display:flex;justify-content:space-between;gap:12px;font-size:.88rem}.x .n{font-weight:600;word-break:break-all}.x .st{color:var(--mute);white-space:nowrap;font-variant-numeric:tabular-nums}
.x.error .st{color:var(--bad)}.x.done .st{color:var(--ok)}
.bar{height:5px;background:var(--line);border-radius:3px;margin-top:9px;overflow:hidden;position:relative}
.bar i{position:absolute;inset:0 auto 0 0;width:0;background:var(--acc);border-radius:3px;transition:width .2s}
.bar.ind i{width:35%;animation:slide 1.1s ease-in-out infinite}
@keyframes slide{from{left:-35%}to{left:100%}}
@media(prefers-reduced-motion:reduce){.bar.ind i{animation:none;width:100%;opacity:.5}}
@media(max-width:820px){.app{grid-template-columns:1fr}
 aside{position:static;height:auto;flex-direction:row;align-items:center;overflow-x:auto;padding:10px 12px;gap:2px}
 .brand{padding:0 12px 0 4px;font-size:1.15rem}.nv{width:auto;white-space:nowrap}.me{margin:0 0 0 auto}.me span{display:none}.two{grid-template-columns:1fr}}
"""

DASH_BODY = r"""</style></head><body>
<div class="app">
<aside>
 <div class="brand">My Cloud</div>
 <button class="nv" id="n-files">Files</button><button class="nv" id="n-add">Add files</button>
 <button class="nv" id="n-subs">Subtitles</button><button class="nv" id="n-storage">Storage</button>
 <div class="me"><span id="who"></span><form id="lo" method="post" action="/logout"><button>Sign out</button></form></div>
</aside>
<main>

<section id="v-files">
 <h1>Your files</h1>
 <div class="panel pad">
  <div class="cap-t" id="capText">Loading storage…</div>
  <div class="cap" id="capBar"></div>
  <div class="leg" id="capLeg"></div>
 </div>
 <div class="tools"><input type="text" id="q" placeholder="Search files" aria-label="Search files"><select id="fpool" aria-label="Filter by account"></select><span class="c" id="cnt"></span></div>
 <div class="panel" id="list"><div class="empty">Loading…</div></div>
</section>

<section id="v-add" hidden>
 <h1>Add files</h1>
 <p class="lead">Upload from this device or let the server fetch a link. Each file is saved to one storage account.</p>
 <div class="panel pad" style="margin-bottom:16px"><label class="l" for="upool" style="margin-top:0">Save to</label><select id="upool"></select></div>
 <div class="two">
  <div class="panel pad">
   <h2>From this device</h2>
   <input type="text" id="dname" placeholder="Save as (optional, single file only)" aria-label="File name" style="margin-bottom:12px">
   <label class="drop" id="drop" for="pick"><b>Drop files here or choose them</b><span>Up to 20&nbsp;GB each. Videos work best as MP4.</span></label>
   <input type="file" id="pick" multiple hidden>
  </div>
  <div class="panel pad">
   <h2>From a link</h2>
   <textarea id="urls" placeholder="https://example.com/video.mp4&#10;One link per line" aria-label="File links"></textarea>
   <input type="text" id="rname" placeholder="Save as (optional, single link only)" aria-label="File name" style="margin-top:10px">
   <p class="hint">The server downloads the file directly, so nothing passes through your device.</p>
   <button class="btn" id="fetch" style="margin-top:12px">Fetch to cloud</button>
  </div>
 </div>
</section>

<section id="v-subs" hidden>
 <h1>Subtitles</h1>
 <p class="lead">Combine a video and a subtitle file from storage or from links. The result is saved back to your cloud.</p>
 <div class="panel pad">
  <div class="seg" id="mode"><button type="button" data-m="soft" aria-pressed="true">Selectable track</button><button type="button" data-m="burn" aria-pressed="false">Burned into picture</button></div>
  <fieldset class="src" id="srcV"><legend>Video</legend>
   <div class="seg"><button type="button" data-m="storage" aria-pressed="true">From storage</button><button type="button" data-m="url" aria-pressed="false">From link</button></div>
   <div class="pk"><input type="text" class="pk-in" role="combobox" aria-expanded="false" autocomplete="off" placeholder="Search your videos" aria-label="Search your videos"><div class="pk-list" role="listbox" hidden></div></div>
   <input type="text" class="u-in" placeholder="https://…/movie.mkv" aria-label="Video link" hidden>
  </fieldset>
  <fieldset class="src" id="srcS"><legend>Subtitle file (.srt, .ass, .ssa, .vtt)</legend>
   <div class="seg"><button type="button" data-m="storage" aria-pressed="true">From storage</button><button type="button" data-m="url" aria-pressed="false">From link</button></div>
   <div class="pk"><input type="text" class="pk-in" role="combobox" aria-expanded="false" autocomplete="off" placeholder="Search your subtitle files" aria-label="Search your subtitle files"><div class="pk-list" role="listbox" hidden></div></div>
   <input type="text" class="u-in" placeholder="https://…/movie.srt" aria-label="Subtitle link" hidden>
  </fieldset>
  <div class="grid"><div><label class="l" for="oname" style="margin-top:0">Save as</label><input type="text" id="oname" placeholder="movie_sub.mkv"></div></div>
  <div class="grid" id="optsSoft" style="margin-top:4px"><div><label class="l" for="lang">Language code</label><input type="text" id="lang" value="si"></div><div><label class="l" for="tname">Track name</label><input type="text" id="tname" value="සිංහල | Sinhala"></div></div>
  <div class="grid" id="optsBurn" style="margin-top:4px" hidden>
   <div><label class="l" for="hfont">Font</label><input type="text" id="hfont" value="Noto Sans Sinhala"></div>
   <div><label class="l" for="hsize">Font size</label><input type="number" id="hsize" value="22" min="8" max="72"></div>
   <div><label class="l" for="hcrf">Quality</label><select id="hcrf"><option value="18">High (larger file)</option><option value="21" selected>Balanced</option><option value="25">Smaller file</option></select></div>
   <div><label class="l" for="hpre">Speed</label><select id="hpre"><option value="ultrafast">Fastest (bigger file)</option><option value="veryfast" selected>Fast</option><option value="medium">Slow (smaller file)</option></select></div>
  </div>
  <p class="hint" id="modeHint"></p>
  <button class="btn" id="go" style="margin-top:14px">Merge subtitles and save</button>
 </div>
</section>

<section id="v-storage" hidden>
 <h1>Storage</h1>
 <p class="lead">Each account is a Hugging Face token and one dataset. Connect more accounts to grow your cloud past the 100&nbsp;GB limit of a single dataset.</p>
 <div class="panel pad">
  <h2>Connect an account</h2>
  <div class="grid">
   <div><label class="l" for="plabel" style="margin-top:0">Name (optional)</label><input type="text" id="plabel" placeholder="Account 2" autocomplete="off"></div>
   <div><label class="l" for="prepo" style="margin-top:0">Dataset</label><input type="text" id="prepo" placeholder="username/my-dataset" autocomplete="off"></div>
   <div><label class="l" for="ptoken" style="margin-top:0">Hugging Face token (write access)</label><input type="password" id="ptoken" placeholder="hf_…" autocomplete="off"></div>
   <div><label class="l" for="plimit" style="margin-top:0">Capacity (GB)</label><input type="number" id="plimit" value="95" min="1"></div>
  </div>
  <label class="chk"><input type="checkbox" id="pcreate" checked> Create the dataset if it doesn't exist</label>
  <p class="hint">The token is checked by saving a small test file. Tokens are stored encrypted. The dataset must be public for stream and download links to open.</p>
  <button class="btn" id="padd" style="margin-top:12px">Connect account</button>
  <div class="perr" id="perr" role="alert"></div>
 </div>
 <div class="pools" id="plist"></div>
</section>

</main></div>
<dialog id="dlg"><form method="dialog"><button class="btn sm">Close</button></form><video id="vid" controls playsinline></video></dialog>
<div id="xfers" aria-live="polite"></div><div id="toast" role="status"></div>
<script>
const $=id=>document.getElementById(id);
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmt=b=>b<1024?b+' B':b<1048576?(b/1024).toFixed(1)+' KB':b<1073741824?(b/1048576).toFixed(1)+' MB':(b/1073741824).toFixed(2)+' GB';
const GB=1073741824,COLORS=['#17594A','#3B5BDB','#B7791F','#9C36B5','#C2255C','#0B7285','#5F3DC4','#2B8A3E'];
const isVid=n=>/\.(mp4|webm|mov|m4v|mkv|ogv)$/i.test(n);
let FILES=[],POOLS=[];
const pool=id=>POOLS.find(p=>p.id===id);
const col=id=>COLORS[Math.max(0,POOLS.findIndex(p=>p.id===id))%COLORS.length];
function toast(m){const t=$('toast');t.textContent=m;t.classList.add('on');clearTimeout(t._h);t._h=setTimeout(()=>t.classList.remove('on'),2000)}
async function api(u,o){const r=await fetch(u,Object.assign({credentials:'same-origin'},o));if(r.status===401){location.href='/login?next=%2F';throw new Error('auth')}return r}
const send=(u,b,m)=>api(u,{method:m||'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(b)});
function copy(t){navigator.clipboard.writeText(t).then(()=>toast('Link copied'),()=>toast('Copy failed'))}

/* navigation */
const VIEWS=['files','add','subs','storage'];
function go(v){if(!VIEWS.includes(v))v='files';VIEWS.forEach(x=>{$('v-'+x).hidden=x!==v;$('n-'+x).setAttribute('aria-current',x===v?'page':'false')});history.replaceState(null,'','#'+v);window.scrollTo(0,0);if(v==='storage'||v==='files')load()}
VIEWS.forEach(v=>$('n-'+v).onclick=()=>go(v));

/* activity tray */
function xfer(name){const d=document.createElement('div');d.className='x';d.innerHTML='<div class="top"><span class="n"></span><span class="st">Starting</span></div><div class="bar"><i></i></div>';d.querySelector('.n').textContent=name;$('xfers').prepend(d);
 return{set(st,p,ind){d.querySelector('.st').textContent=st;const b=d.querySelector('.bar');b.classList.toggle('ind',!!ind);if(p!=null)b.firstChild.style.width=p+'%'},end(cls,st){d.className='x '+cls;d.querySelector('.st').textContent=st;d.querySelector('.bar').style.display='none';setTimeout(()=>d.remove(),cls==='done'?6000:20000)}}}
async function poll(id,x){const r=await api('/api/jobs/'+id);const j=await r.json();
 if(j.label&&j.stage!=='done'&&j.stage!=='error')x.set(j.label,j.pct,j.pct==null);
 else if(j.stage==='downloading')x.set('Downloading '+(j.total?Math.round(j.done/j.total*100)+'% · ':'')+fmt(j.speed)+'/s',j.total?j.done/j.total*100:null,!j.total);
 else if(j.stage==='uploading')x.set('Saving to storage…',100,true);
 else if(j.stage==='done'){x.end('done','Done');toast('Saved '+j.name);load();return}
 else if(j.stage==='error'){x.end('error',j.error||'Failed');return}
 setTimeout(()=>poll(id,x),700)}

/* files */
function renderCap(){const tot=POOLS.reduce((a,p)=>a+p.limit_gb*GB,0),used=POOLS.reduce((a,p)=>a+p.used,0);
 if(!POOLS.length){$('capText').textContent='No storage connected yet. Add an account on the Storage page.';$('capBar').innerHTML='';$('capLeg').innerHTML='';return}
 $('capText').textContent=fmt(used)+' used of '+fmt(tot)+' across '+POOLS.length+(POOLS.length>1?' accounts':' account');
 $('capBar').innerHTML=POOLS.map(p=>{const l=p.limit_gb*GB;return '<i style="flex:'+l+'" title="'+esc(p.label)+'"><b style="width:'+Math.min(100,p.used/l*100)+'%;background:'+col(p.id)+'"></b></i>'}).join('');
 $('capLeg').innerHTML=POOLS.map(p=>'<span><span class="dot" style="background:'+col(p.id)+'"></span>'+esc(p.label)+' <em>'+fmt(p.used)+' of '+p.limit_gb+' GB</em></span>').join('')}
function fillSelects(){const a=$('upool'),b=$('fpool'),av=a.value,bv=b.value;
 a.innerHTML='<option value="">Automatic (most free space)</option>'+POOLS.filter(p=>p.enabled).map(p=>'<option value="'+esc(p.id)+'">'+esc(p.label)+' · '+fmt(p.free)+' free</option>').join('');
 b.innerHTML='<option value="">All accounts</option>'+POOLS.map(p=>'<option value="'+esc(p.id)+'">'+esc(p.label)+'</option>').join('');
 a.value=av;b.value=bv}
function renderFiles(){const q=$('q').value.toLowerCase(),pf=$('fpool').value,L=FILES.filter(f=>f.name.toLowerCase().includes(q)&&(!pf||f.pool===pf));
 $('cnt').textContent=FILES.length?L.length+' of '+FILES.length+' files':'';
 if(!L.length){$('list').innerHTML='<div class="empty">'+(FILES.length?'No files match your search.':'No files yet. Open Add files to upload your first one.')+'</div>';$('list')._L=[];return}
 $('list').innerHTML=L.map((f,i)=>{const p=pool(f.pool);return '<div class="f"><div><div class="n">'+esc(f.name)+'</div><div class="m"><span class="dot" style="background:'+col(f.pool)+';width:8px;height:8px;margin:0"></span>'+esc(p?p.label:'Unknown account')+'</div></div><span class="sz">'+fmt(f.size)+'</span><span class="a">'+(isVid(f.name)?'<button class="btn sm" data-a="play" data-i="'+i+'">Play</button>':'')+'<button class="btn ghost sm" data-a="cdn" data-i="'+i+'">Copy stream link</button><button class="btn ghost sm" data-a="dl" data-i="'+i+'">Copy download link</button><button class="btn ghost sm danger" data-a="del" data-i="'+i+'">Delete</button></span></div>'}).join('');
 $('list')._L=L}
$('list').onclick=async e=>{const b=e.target.closest('button');if(!b)return;const f=$('list')._L[+b.dataset.i],a=b.dataset.a;
 if(a==='cdn')copy(f.cdn_url);else if(a==='dl')copy(f.download_url);
 else if(a==='play'){$('vid').src=f.cdn_url;$('dlg').showModal();$('vid').play().catch(()=>{})}
 else if(a==='del'&&confirm('Delete '+f.name+'? This cannot be undone.')){const r=await api('/api/files/'+encodeURIComponent(f.name),{method:'DELETE'});if(r.ok){toast('Deleted');load()}else toast('Delete failed')}};
$('dlg').addEventListener('close',()=>{$('vid').pause();$('vid').removeAttribute('src');$('vid').load()});
$('q').oninput=renderFiles;$('fpool').onchange=renderFiles;
async function load(){try{const [a,b]=await Promise.all([api('/api/files'),api('/api/pools')]);const j=await a.json(),k=await b.json();
 FILES=j.items||[];POOLS=k.pools||[];if(j.error)toast(j.error);renderCap();fillSelects();renderFiles();renderPools()}catch(e){}}

/* add files */
function upload(file,name){name=name||file.name;const x=xfer(name),t0=Date.now(),r=new XMLHttpRequest();
 r.open('POST','/api/upload?name='+encodeURIComponent(name)+'&pool='+encodeURIComponent($('upool').value));
 r.upload.onprogress=e=>{if(!e.lengthComputable)return;const p=e.loaded/e.total*100,s=e.loaded/((Date.now()-t0)/1000||1);x.set(p<100?Math.round(p)+'% · '+fmt(s)+'/s':'Saving to storage…',p,p>=100)};
 r.onload=()=>{if(r.status===200){x.end('done','Done');toast('Uploaded '+name);load()}else if(r.status===401)location.href='/login';else{let m='Upload failed';try{m=JSON.parse(r.responseText).detail||m}catch(e){}x.end('error',m)}};
 r.onerror=()=>x.end('error','Network error');r.send(file)}
const drop=$('drop');['dragover','dragenter'].forEach(e=>drop.addEventListener(e,ev=>{ev.preventDefault();drop.classList.add('over')}));
['dragleave','drop'].forEach(e=>drop.addEventListener(e,ev=>{ev.preventDefault();drop.classList.remove('over')}));
function many(fs){fs=[...fs];const n=$('dname').value.trim();fs.forEach(f=>{let nm='';if(fs.length===1&&n){const i=f.name.lastIndexOf('.');nm=n.includes('.')||i<0?n:n+f.name.slice(i)}upload(f,nm)});$('dname').value=''}
drop.addEventListener('drop',e=>many(e.dataTransfer.files));$('pick').onchange=e=>{many(e.target.files);e.target.value=''};
$('fetch').onclick=async()=>{const urls=$('urls').value.split(/\s+/).filter(Boolean);if(!urls.length)return toast('Paste at least one link');
 const name=urls.length===1?$('rname').value.trim():'';$('fetch').disabled=true;
 for(const url of urls){const x=xfer(url.split('/').pop()||url);
  try{const r=await send('/api/remote',{url,name,pool:$('upool').value});const j=await r.json();
   if(!r.ok){x.end('error',j.detail||'Rejected');continue}poll(j.id,x)}catch(e){x.end('error','Request failed')}}
 $('urls').value='';$('rname').value='';$('fetch').disabled=false};

/* subtitles */
const SUBX=['srt','ass','ssa','vtt'],VIDX=['mkv','mp4','m4v','mov','webm','avi','ogv'];
const ext=n=>{const i=n.lastIndexOf('.');return i<0?'':n.slice(i+1).toLowerCase()};
let MODE='soft',LASTV='';
function mkSrc(root,exts,onPick){let mode='storage',sel=null;const inp=root.querySelector('.pk-in'),lst=root.querySelector('.pk-list'),uin=root.querySelector('.u-in'),box=root.querySelector('.pk');
 function show(){const q=inp.value.toLowerCase(),L=FILES.filter(f=>exts.includes(ext(f.name))&&f.name.toLowerCase().includes(q)).slice(0,60);
  lst.innerHTML=L.length?L.map((f,i)=>'<div role="option" data-i="'+i+'"><span>'+esc(f.name)+'</span><small>'+fmt(f.size)+'</small></div>').join(''):'<div class="none">No matching files in storage</div>';lst._L=L;lst.hidden=false;inp.setAttribute('aria-expanded','true')}
 function hide(){lst.hidden=true;inp.setAttribute('aria-expanded','false')}
 function choose(f){sel=f.name;inp.value=f.name;hide();if(onPick)onPick(f.name)}
 inp.addEventListener('focus',show);inp.addEventListener('blur',hide);inp.addEventListener('input',()=>{sel=null;show()});
 inp.addEventListener('keydown',e=>{if(e.key==='Escape')hide();if(e.key==='Enter'&&!lst.hidden&&(lst._L||[]).length){e.preventDefault();choose(lst._L[0])}});
 lst.addEventListener('mousedown',e=>{const d=e.target.closest('[data-i]');if(d){e.preventDefault();choose(lst._L[+d.dataset.i])}});
 root.querySelectorAll('.seg button').forEach(b=>b.onclick=()=>{mode=b.dataset.m;root.querySelectorAll('.seg button').forEach(x=>x.setAttribute('aria-pressed',x===b));box.hidden=mode!=='storage';uin.hidden=mode!=='url'});
 return{get(){if(mode==='url'){const v=uin.value.trim();return v?{type:'url',value:v}:null}const n=sel||(FILES.find(f=>f.name===inp.value)||{}).name;return n?{type:'storage',value:n}:null}}}
function suggest(){const o=$('oname');if(o._m||!LASTV)return;const i=LASTV.lastIndexOf('.'),s=i>0?LASTV.slice(0,i):LASTV;o.value=s+(MODE==='soft'?'_sub.mkv':'_hardsub.mp4')}
const vs=mkSrc($('srcV'),VIDX,n=>{LASTV=n;suggest()}),ss=mkSrc($('srcS'),SUBX);
$('oname').addEventListener('input',e=>{e.target._m=!!e.target.value});
function setMode(m){MODE=m;document.querySelectorAll('#mode button').forEach(b=>b.setAttribute('aria-pressed',b.dataset.m===m));
 $('optsSoft').hidden=m!=='soft';$('optsBurn').hidden=m!=='burn';
 $('go').textContent=m==='soft'?'Merge subtitles and save':'Burn subtitles and save';
 $('oname').placeholder=m==='soft'?'movie_sub.mkv':'movie_hardsub.mp4';
 $('modeHint').textContent=m==='soft'?'Adds the subtitle as a track viewers can switch on or off. The video is not re-encoded, so it is fast. Output is .mkv.':'Draws the subtitle into the picture so it shows in every player. This re-encodes the video (H.264 and AAC, output .mp4) and can take a long time.';
 suggest()}
document.querySelectorAll('#mode button').forEach(b=>b.onclick=()=>setMode(b.dataset.m));setMode('soft');
$('go').onclick=async()=>{const v=vs.get(),s=ss.get();if(!v)return toast('Choose a video');if(!s)return toast('Choose a subtitle file');
 const name=$('oname').value.trim(),soft=MODE==='soft';$('go').disabled=true;const x=xfer(name||v.value.split('/').pop());
 const body=soft?{video:v,sub:s,name,lang:$('lang').value.trim()||'si',track:$('tname').value.trim()}:{video:v,sub:s,name,font:$('hfont').value.trim(),size:$('hsize').value.trim(),crf:$('hcrf').value,preset:$('hpre').value};
 try{const r=await send(soft?'/api/subtitle':'/api/hardsub',body);const j=await r.json();if(!r.ok)x.end('error',j.detail||'Rejected');else poll(j.id,x)}catch(e){x.end('error','Request failed')}
 $('go').disabled=false};

/* storage accounts */
function renderPools(){const el=$('plist');
 if(!POOLS.length){el.innerHTML='<div class="panel empty">No accounts yet. Connect your first Hugging Face dataset above.</div>';return}
 el.innerHTML=POOLS.map(p=>{const l=p.limit_gb*GB,pct=Math.min(100,p.used/l*100),c=col(p.id),st=p.error?'<span class="badge bad">Unreachable</span>':p.enabled?'<span class="badge on">Accepting uploads</span>':'<span class="badge">Paused</span>';
 return '<article class="panel pool" data-id="'+esc(p.id)+'"><div class="ph"><span class="dot" style="background:'+c+'"></span><div><h3>'+esc(p.label)+'</h3><a href="https://huggingface.co/datasets/'+esc(p.repo)+'" target="_blank" rel="noopener">'+esc(p.repo)+'</a></div>'+st+'</div>'
 +'<div class="bar2"><b style="width:'+pct+'%;background:'+c+'"></b></div><p class="meta">'+fmt(p.used)+' of '+p.limit_gb+' GB used · '+p.count+' files · token '+esc(p.token_hint)+'</p>'
 +(p.error?'<p class="warn bad">Cannot reach this dataset: '+esc(p.error)+'</p>':'')
 +(p.private?'<p class="warn">This dataset is private, so stream and download links will not open. Make it public on Hugging Face.</p>':'')
 +(p.source==='env'?'<p class="hint">Main account. Its name and capacity are set in the server settings.</p>':'<div class="a"><button class="btn ghost sm" data-a="tog">'+(p.enabled?'Pause uploads':'Resume uploads')+'</button><button class="btn ghost sm" data-a="ed">Edit</button><button class="btn ghost sm danger" data-a="rm">Remove</button></div>')+'</article>'}).join('')}
$('plist').onclick=async e=>{const b=e.target.closest('button');if(!b)return;const id=b.closest('.pool').dataset.id,p=pool(id),a=b.dataset.a;let r;
 if(a==='tog')r=await send('/api/pools/'+id,{enabled:!p.enabled},'PATCH');
 else if(a==='ed'){const label=prompt('Account name',p.label);if(label===null)return;const lim=prompt('Capacity in GB',p.limit_gb);if(lim===null)return;r=await send('/api/pools/'+id,{label,limit_gb:lim},'PATCH')}
 else if(a==='rm'){if(!confirm('Remove '+p.label+' from My Cloud?\n\nIts files stay on Hugging Face but will no longer appear here.'))return;r=await api('/api/pools/'+id,{method:'DELETE'})}
 if(r&&r.ok){toast('Saved');load()}else if(r){let m='Could not save';try{m=(await r.json()).detail||m}catch(_){}toast(m)}};
$('padd').onclick=async()=>{$('perr').textContent='';const b={label:$('plabel').value,repo:$('prepo').value,token:$('ptoken').value,limit_gb:$('plimit').value,create:$('pcreate').checked};
 if(!b.repo.trim()||!b.token.trim()){$('perr').textContent='Enter the dataset name and a token.';return}
 $('padd').disabled=true;$('padd').textContent='Connecting…';
 try{const r=await send('/api/pools',b),j=await r.json();
  if(!r.ok)$('perr').textContent=j.detail||'Could not connect this account.';
  else{toast('Connected '+j.label);['plabel','prepo','ptoken'].forEach(i=>$(i).value='');load()}}catch(e){}
 $('padd').disabled=false;$('padd').textContent='Connect account'};

(async()=>{try{const m=await(await fetch('/api/me')).json();if(m.auth_enabled&&!m.authenticated)return location.href='/login?next=%2F';$('who').textContent=m.auth_enabled?m.username:'';if(!m.auth_enabled)$('lo').remove()}catch(e){}
 go(location.hash.slice(1))})();
window.addEventListener('hashchange',()=>go(location.hash.slice(1)));
</script></body></html>"""

DASHBOARD_HTML = ('<!DOCTYPE html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">'
                  '<title>My Cloud</title>' + FONT + "<style>" + BASE_CSS + DASH_CSS + DASH_BODY)

def render_login(error="", next_url="/"):
    import html
    err = f'<div class="err">{html.escape(error)}</div>' if error else ""
    return LOGIN_HTML.replace("%%ERROR%%", err).replace("%%NEXT%%", html.escape(safe_next(next_url), quote=True))

# ───────────────────────── Routes ─────────────────────────
@app.get("/", response_class=HTMLResponse)
def dashboard(request: Request):
    if AUTH_ENABLED and not get_current_user(request):
        return RedirectResponse("/login?next=%2F", 302)
    return HTMLResponse(DASHBOARD_HTML)

@app.get("/login", response_class=HTMLResponse)
def login_page(request: Request, next: str = "/"):
    if not AUTH_ENABLED or get_current_user(request):
        return RedirectResponse(safe_next(next) if AUTH_ENABLED else "/", 302)
    return HTMLResponse(render_login("", next))

@app.post("/login", response_class=HTMLResponse)
async def login_submit(request: Request, username: str = Form(""), password: str = Form(""), next: str = Form("/")):
    if not AUTH_ENABLED:
        return RedirectResponse("/", 302)
    username = username.strip()
    ip = request.client.host if request.client else "?"
    key, now = f"{ip}|{username}", time.time()
    rec = failed.get(key)
    if rec and rec[1] > now:
        return HTMLResponse(render_login("Too many attempts. Try again in a few minutes.", next), 429)
    if len(failed) > 10000:
        failed.clear()
    if username == ADMIN_USERNAME and verify_password(password, PASSWORD_HASH):
        failed.pop(key, None)
        resp = RedirectResponse(safe_next(next), 302)
        resp.set_cookie(COOKIE_NAME, create_session_token(username), max_age=SESSION_MAX_AGE,
                        httponly=True, samesite="lax", secure=is_https(request), path="/")
        return resp
    n = rec[0] + 1 if rec and rec[1] == 0 else 1
    failed[key] = (n, now + LOCK_SECONDS if n >= MAX_FAILED else 0)
    return HTMLResponse(render_login("Wrong username or password.", next), 401)

@app.post("/logout")
def logout():
    resp = RedirectResponse("/", 302)
    resp.delete_cookie(COOKIE_NAME, path="/")
    return resp

@app.get("/health")
def health():
    return {"status": "ok", "time": time.time(), "pools": len(POOLS), "auth_enabled": AUTH_ENABLED,
            "telegram_ok": tg_state["ok"], "mkvmerge": bool(shutil.which("mkvmerge")),
            "ffmpeg": bool(shutil.which("ffmpeg")), "fast_upload": os.environ.get("HF_HUB_ENABLE_HF_TRANSFER") == "1",
            **({"telegram_error": tg_state["error"]} if DEBUG_ERRORS else {})}

@app.get("/api/me")
def api_me(request: Request):
    user = get_current_user(request)
    return {"auth_enabled": AUTH_ENABLED, "authenticated": bool(user) or not AUTH_ENABLED,
            "username": user or "anonymous"}

# ── files
@app.get("/api/files")
async def api_files(request: Request):
    require_login(request)
    if not POOLS:
        return {"items": [], "error": "No storage account is connected yet"}
    try:
        items = []
        for f in await list_files():
            items.append({**f, **links(f["name"], request, POOLS.get(f["pool"]))})
        return {"items": items, "count": len(items)}
    except Exception as e:
        log.error("List failed: %s", e)
        return {"items": [], "error": str(e)}

@app.delete("/api/files/{name:path}")
async def api_delete(request: Request, name: str):
    require_login(request)
    name = safe_name(name)
    pool = await locate(name)
    if not pool:
        raise HTTPException(404, "File not found")
    try:
        await asyncio.to_thread(pool.api.delete_file, path_in_repo=name, repo_id=pool.repo,
                                repo_type="dataset", commit_message=f"Delete: {name}")
    except Exception as e:
        raise HTTPException(500, str(e))
    _cache["t"] = 0
    return {"success": True}

@app.post("/api/upload")
async def api_upload(request: Request, name: str = "", pool: str = ""):
    """Raw-body upload: the browser sends the file bytes directly, we stream them to disk."""
    require_login(request)
    if not POOLS:
        raise HTTPException(500, "No storage account is connected yet")
    try:
        fname = safe_name(name)
    except HTTPException:
        fname = f"file_{uuid.uuid4().hex[:8]}"
    declared = int(request.headers.get("content-length") or 0)
    if declared > MAX_FILE_SIZE:
        raise HTTPException(413, "File is larger than the size limit")
    await pick(declared, fname, pool)  # fail before receiving gigabytes
    tmp, size = pick_tmp(declared) / f"{uuid.uuid4().hex}_{fname}", 0
    try:
        async with aiofiles.open(tmp, "wb") as out:
            async for chunk in request.stream():
                size += len(chunk)
                if size > MAX_FILE_SIZE:
                    raise HTTPException(413, "File is larger than the size limit")
                await out.write(chunk)
        if size == 0:
            raise HTTPException(400, "Empty upload")
        target = await pick(size, fname, pool)
        t0 = time.time()
        await push_to_hf(tmp, fname, "Web upload", target)
        log.info("Web upload %s: %.1f MB -> %s in %.1fs", fname, size / 1048576, target.label, time.time() - t0)
        return {"success": True, "filename": fname, "size": size, "account": target.label, **links(fname, request, target)}
    except HTTPException:
        raise
    except Exception as e:
        log.error("Web upload failed: %s", e)
        raise HTTPException(500, str(e))
    finally:
        tmp.unlink(missing_ok=True)

@app.post("/api/remote")
async def api_remote(request: Request):
    require_login(request)
    if not POOLS:
        raise HTTPException(500, "No storage account is connected yet")
    body = await request.json()
    url, name = str(body.get("url", "")).strip(), str(body.get("name", "")).strip()
    preferred = str(body.get("pool") or "").strip()
    try:
        await assert_public(url)
        if name:
            safe_name(name)
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(400, str(e) or "Invalid link")
    job = new_job(name or url)
    asyncio.create_task(run_remote(job, url, name, preferred))
    return {"id": job["id"]}

async def parse_sources(b: dict) -> list:
    srcs = []
    for key in ("video", "sub"):
        src = b.get(key) or {}
        kind, val = src.get("type"), str(src.get("value", "")).strip()
        if kind not in ("storage", "url") or not val:
            raise HTTPException(400, f"Choose a {key if key == 'video' else 'subtitle'} source")
        if kind == "url":
            try:
                await assert_public(val)
            except Exception as e:
                raise HTTPException(400, str(e) or "Invalid link")
        else:
            safe_name(val)
        srcs.append({"type": kind, "value": val})
    return srcs

@app.post("/api/subtitle")
async def api_subtitle(request: Request):
    require_login(request)
    if not POOLS:
        raise HTTPException(500, "No storage account is connected yet")
    b = await request.json()
    srcs = await parse_sources(b)
    lang = str(b.get("lang") or "si").strip()
    if not re.fullmatch(r"[A-Za-z]{2,3}(-[A-Za-z0-9]{2,8})?", lang):
        raise HTTPException(400, "Language must be an ISO code such as si or en")
    track = " ".join(str(b.get("track") or "").split())[:120]
    name = str(b.get("name") or "").strip()
    job = new_job(name or "subtitle merge")
    asyncio.create_task(run_mux(job, srcs[0], srcs[1], name, lang, track))
    return {"id": job["id"]}

@app.post("/api/hardsub")
async def api_hardsub(request: Request):
    require_login(request)
    if not POOLS:
        raise HTTPException(500, "No storage account is connected yet")
    b = await request.json()
    srcs = await parse_sources(b)
    font = str(b.get("font") or "Noto Sans Sinhala").strip()
    if not re.fullmatch(r"[A-Za-z0-9 _-]{1,60}", font):
        raise HTTPException(400, "Font name may only contain letters, numbers, spaces, - and _")
    try:
        size = max(8, min(72, int(b.get("size") or 22)))
        crf = max(16, min(30, int(b.get("crf") or 21)))
    except (TypeError, ValueError):
        raise HTTPException(400, "Font size and quality must be numbers")
    preset = b.get("preset") if b.get("preset") in {"ultrafast", "veryfast", "faster", "medium"} else "veryfast"
    name = str(b.get("name") or "").strip()
    job = new_job(name or "hardcode subtitles")
    asyncio.create_task(run_burn(job, srcs[0], srcs[1], name, font, size, crf, preset))
    return {"id": job["id"]}

@app.get("/api/jobs/{job_id}")
def api_job(request: Request, job_id: str):
    require_login(request)
    job = JOBS.get(job_id)
    if not job:
        raise HTTPException(404, "Unknown job")
    return job

# ── storage pools
def _connect_sync(token: str, repo: str, create: bool):
    api = HfApi(token=token)
    who = api.whoami()["name"]
    repo = re.sub(r"^https?://huggingface\.co/datasets/", "", repo).strip("/")
    if "/" not in repo:
        repo = f"{who}/{repo}"
    try:
        info = api.repo_info(repo_id=repo, repo_type="dataset")
    except RepositoryNotFoundError:
        if not create:
            raise ValueError("That dataset doesn't exist. Tick \"Create the dataset\" or create it on Hugging Face first.")
        api.create_repo(repo_id=repo, repo_type="dataset", private=False, exist_ok=True)
        info = api.repo_info(repo_id=repo, repo_type="dataset")
    api.upload_file(path_or_fileobj=b"ok", path_in_repo=".mycloud/ping", repo_id=repo, repo_type="dataset",
                    commit_message="Connect to My Cloud")
    return repo, bool(getattr(info, "private", False))

@app.get("/api/pools")
async def api_pools(request: Request):
    require_login(request)
    await list_files(5)
    return {"pools": [p.public() for p in POOLS.values()]}

@app.post("/api/pools")
async def api_pool_add(request: Request):
    require_login(request)
    b = await request.json()
    token, repo = str(b.get("token", "")).strip(), str(b.get("repo", "")).strip()
    label = " ".join(str(b.get("label") or "").split())[:40]
    try:
        limit = float(b.get("limit_gb") or DEFAULT_LIMIT_GB)
    except (TypeError, ValueError):
        raise HTTPException(400, "Capacity must be a number of GB")
    if not token or not repo:
        raise HTTPException(400, "Enter the dataset name and a token")
    if limit < 1:
        raise HTTPException(400, "Capacity must be at least 1 GB")
    try:
        repo_id, private = await asyncio.to_thread(_connect_sync, token, repo, bool(b.get("create", True)))
    except ValueError as e:
        raise HTTPException(400, str(e))
    except Exception as e:
        raise HTTPException(400, f"Could not connect: {str(e)[:220] or type(e).__name__}")
    if any(p.repo.lower() == repo_id.lower() for p in POOLS.values()):
        raise HTTPException(400, f"{repo_id} is already connected")
    pool = Pool(uuid.uuid4().hex[:8], token, repo_id, label, limit, True, "ui", private)
    POOLS[pool.id] = pool
    try:
        await asyncio.to_thread(_save_cfg_sync)
    except Exception as e:
        POOLS.pop(pool.id, None)
        log.error("Saving pools failed: %s", e)
        raise HTTPException(500, f"Connected, but could not save the account: {str(e)[:200]}")
    _cache["t"] = 0
    return pool.public()

@app.patch("/api/pools/{pid}")
async def api_pool_edit(request: Request, pid: str):
    require_login(request)
    p = POOLS.get(pid)
    if not p:
        raise HTTPException(404, "Unknown account")
    if p.source == "env":
        raise HTTPException(400, "The main account is configured in the server settings")
    b = await request.json()
    old = (p.label, p.limit_gb, p.enabled)
    if "label" in b:
        p.label = " ".join(str(b["label"]).split())[:40] or p.label
    if "limit_gb" in b:
        try:
            lim = float(b["limit_gb"])
        except (TypeError, ValueError):
            raise HTTPException(400, "Capacity must be a number of GB")
        if lim < 1:
            raise HTTPException(400, "Capacity must be at least 1 GB")
        p.limit_gb = lim
    if "enabled" in b:
        p.enabled = bool(b["enabled"])
    try:
        await asyncio.to_thread(_save_cfg_sync)
    except Exception as e:
        p.label, p.limit_gb, p.enabled = old
        raise HTTPException(500, f"Could not save: {str(e)[:200]}")
    return p.public()

@app.delete("/api/pools/{pid}")
async def api_pool_remove(request: Request, pid: str):
    require_login(request)
    p = POOLS.get(pid)
    if not p:
        raise HTTPException(404, "Unknown account")
    if p.source == "env":
        raise HTTPException(400, "The main account is configured in the server settings")
    POOLS.pop(pid)
    try:
        await asyncio.to_thread(_save_cfg_sync)
    except Exception as e:
        POOLS[pid] = p
        raise HTTPException(500, f"Could not save: {str(e)[:200]}")
    _cache["t"] = 0
    return {"success": True}

# ── public links (resolved to whichever account holds the file)
@app.get("/cdn/{filename:path}")
async def cdn(request: Request, filename: str):
    guard = download_guard(request)
    if guard:
        return guard
    name = safe_name(filename)
    pool = await locate(name)
    if not pool:
        raise HTTPException(404, "File not found")
    return RedirectResponse(hf_url(name, pool), 302)

@app.get("/download/{filename:path}")
async def download(request: Request, filename: str):
    guard = download_guard(request)
    if guard:
        return guard
    name = safe_name(filename)
    pool = await locate(name)
    if not pool:
        raise HTTPException(404, "File not found")
    return RedirectResponse(hf_url(name, pool, True), 302)

class RemoteStream(io.BufferedIOBase):
    """Seekable file-like object with NO disk usage.

    huggingface_hub must know the sha256 before uploading to LFS, so it reads the
    file once (hash), seeks back to 0, and reads it again (upload). Instead of a
    local file we re-open the remote source (Telegram) at the requested offset,
    so RAM use stays at a few MB and nothing is written to disk.
    """
    ALIGN = 1024 * 1024

    def __init__(self, opener, size: int, loop):
        self._open, self._size, self._loop = opener, int(size), loop
        self._pos, self._it, self._skip = 0, None, 0
        self._buf = bytearray()
        self.bytes_served = 0

    def __len__(self): return self._size
    def readable(self): return True
    def seekable(self): return True
    def tell(self): return self._pos

    def seek(self, offset, whence=io.SEEK_SET):
        if whence == io.SEEK_CUR:
            offset += self._pos
        elif whence == io.SEEK_END:
            offset += self._size
        offset = max(0, min(int(offset), self._size))
        if offset != self._pos:
            self._it, self._buf, self._pos = None, bytearray(), offset
        return self._pos

    def read(self, n=-1):
        left = self._size - self._pos
        n = left if (n is None or n < 0) else min(n, left)
        if n <= 0:
            return b""
        if self._it is None:
            start = self._pos - self._pos % self.ALIGN
            self._it, self._skip, self._buf = self._open(start), self._pos - start, bytearray()
        while len(self._buf) < n:
            try:
                chunk = asyncio.run_coroutine_threadsafe(self._it.__anext__(), self._loop).result()
            except StopAsyncIteration:
                break
            if self._skip:
                cut = min(self._skip, len(chunk))
                chunk, self._skip = chunk[cut:], self._skip - cut
            self._buf += chunk
        out = bytes(self._buf[:n])
        del self._buf[:n]
        self._pos += len(out)
        self.bytes_served += len(out)
        return out

# ───────────────────────── Telegram ─────────────────────────
def register_telegram():
    @client.on(events.NewMessage(pattern="/start"))
    async def _start(event):
        await event.reply("Send me any file and I'll reply with a download link and a streaming link."
                          + (f"\n\nWeb panel: {PUBLIC_BASE_URL}" if PUBLIC_BASE_URL else ""))

    @client.on(events.NewMessage(pattern="/files"))
    async def _files(event):
        if not POOLS:
            return await event.reply("Storage is not configured.")
        try:
            names = [f["name"] for f in await list_files()]
            await event.reply("No files yet." if not names else f"Files ({len(names)}):\n" + "\n".join("• " + n for n in names[:50]))
        except Exception as e:
            await event.reply(f"Error: {e}")

    @client.on(events.NewMessage(pattern="/storage"))
    async def _storage(event):
        if not POOLS:
            return await event.reply("Storage is not configured.")
        try:
            await list_files()
            await event.reply("\n".join(f"• {p.label}: {p.used / 1024**3:.1f} of {p.limit_gb:g} GB"
                                        + ("" if p.enabled else " (paused)") + (" (unreachable)" if p.error else "")
                                        for p in POOLS.values()))
        except Exception as e:
            await event.reply(f"Error: {e}")

    @client.on(events.NewMessage())
    async def _file(event):
        m = event.message
        if not POOLS or not m.file or (m.text or "").startswith("/"):
            return
        status = await event.reply("Preparing…")
        fname = Path(getattr(m.file, "name", None) or "").name
        if not fname:
            ext = ".jpg" if m.photo else (getattr(m.file, "ext", None) or ".bin")
            fname = f"tg_{m.id}{ext if ext.startswith('.') else '.' + ext}"
        total = int(getattr(m.file, "size", 0) or 0)
        last = {"t": 0.0}
        t0 = time.time()

        async def edit(text):
            try:
                await status.edit(text)
            except Exception:
                pass

        try:
            pool = await choose_pool(total, fname)
        except ValueError as e:
            return await edit(f"Failed: {e}")
        tmp = pick_tmp(total) / f"{uuid.uuid4().hex}_{fname}"

        def progress(cur, tot):
            now = time.time()
            if tot and now - last["t"] > 3:
                last["t"] = now
                asyncio.get_running_loop().create_task(
                    edit(f"Downloading {fname}\n{cur * 100 // tot}% · {cur / 1048576 / max(now - t0, .1):.1f} MB/s"))

        if STREAM_UPLOAD and total > 0:
            stream = RemoteStream(
                lambda off: client.iter_download(m.media, offset=off, request_size=1024 * 1024, file_size=total),
                total, asyncio.get_running_loop())

            async def report():
                try:
                    while True:
                        await asyncio.sleep(3)
                        pct = min(99, stream.bytes_served * 100 // (2 * total))
                        await edit(f"Streaming {fname} to {pool.label}\n{pct}% (no disk used)")
                except asyncio.CancelledError:
                    pass

            rep = asyncio.create_task(report())
            try:
                await asyncio.to_thread(pool.api.upload_file, path_or_fileobj=stream, path_in_repo=fname,
                                        repo_id=pool.repo, repo_type="dataset",
                                        commit_message=f"Telegram stream upload: {fname}")
                _cache["t"] = 0
                l = links(fname, pool=pool)
                await edit(f"Done: {fname} ({total / 1048576:.1f} MB) saved to {pool.label}\n\nDownload:\n{l['download_url']}\n\nStream:\n{l['cdn_url']}")
                log.info("TG STREAM upload OK %s: %.1f MB in %.1fs -> %s", fname, total / 1048576, time.time() - t0, pool.label)
                return
            except Exception as e:
                log.warning("Stream upload failed (%s: %s) -> falling back to temp-file mode", type(e).__name__, e)
            finally:
                rep.cancel()

        try:
            await client.download_media(m, file=str(tmp), progress_callback=progress)
            size = tmp.stat().st_size
            t1 = time.time()
            await edit(f"Saving {size / 1048576:.0f} MB to {pool.label}…")
            await push_to_hf(tmp, fname, "Telegram upload", pool)
            l = links(fname, pool=pool)
            await edit(f"Done: {fname} ({size / 1048576:.1f} MB) saved to {pool.label}\n\nDownload:\n{l['download_url']}\n\nStream:\n{l['cdn_url']}")
            log.info("TG upload %s: dl %.1fs, push %.1fs", fname, t1 - t0, time.time() - t1)
        except Exception as e:
            log.error("TG upload failed: %s", e)
            await edit(f"Failed: {type(e).__name__}: {str(e)[:200]}")
        finally:
            tmp.unlink(missing_ok=True)

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=int(os.getenv("PORT", "7860")))
