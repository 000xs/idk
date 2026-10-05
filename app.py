"""My Cloud - Hugging Face dataset storage + Telegram bot + web panel.

requirements.txt:
    fastapi uvicorn[standard] aiofiles httpx telethon cryptg huggingface_hub hf_transfer python-multipart
"""
import os
import io  # noqa: F401  (was missing -> NameError at startup)
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
import zipfile
import traceback
from contextlib import asynccontextmanager
from pathlib import Path, PurePosixPath
from urllib.parse import quote, unquote, urlsplit, urljoin

# Must be set BEFORE huggingface_hub is imported.
# Zero-disk streaming needs the classic LFS path (reads the file object in slices, never all in RAM).
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
from huggingface_hub import HfApi, CommitOperationAdd
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
STREAM_UPLOAD = env_bool("STREAM_UPLOAD", True)  # Telegram -> HF with zero disk
MAX_FILE_SIZE = int(os.getenv("MAX_FILE_SIZE", str(20 * 1024**3)))
MAX_FAILED = int(os.getenv("MAX_FAILED_ATTEMPTS", "5"))
LOCK_SECONDS = int(os.getenv("LOCK_SECONDS", "300"))
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

def hf_url(name: str, download=False) -> str:
    return f"https://huggingface.co/datasets/{HF_REPO}/resolve/main/{quote(safe_name(name))}" + ("?download=true" if download else "")

def links(name: str, request=None) -> dict:
    b, q = base_url(request), quote(safe_name(name))
    return {"download_url": f"{b}/download/{q}" if b else hf_url(name, True),
            "cdn_url": f"{b}/cdn/{q}" if b else hf_url(name)}

# ───────────────────────── HF storage ─────────────────────────
hf_api = HfApi(token=HF_TOKEN) if HF_TOKEN else None
_cache = {"t": 0.0, "items": []}

async def push_to_hf(path, name: str, note: str):
    await asyncio.to_thread(hf_api.upload_file, path_or_fileobj=str(path), path_in_repo=name,
                            repo_id=HF_REPO, repo_type="dataset", commit_message=f"{note}: {name}")
    _cache["t"] = 0

def _list_sync():
    out = []
    for e in hf_api.list_repo_tree(repo_id=HF_REPO, repo_type="dataset", recursive=True):
        size = getattr(e, "size", None)
        if size is None or e.path.startswith(".") or e.path in {"README.md", ".gitattributes"}:
            continue
        out.append({"name": e.path, "size": size})
    return sorted(out, key=lambda x: x["name"].lower())

async def list_files():
    if time.time() - _cache["t"] > 5:
        _cache["items"] = await asyncio.to_thread(_list_sync)
        _cache["t"] = time.time()
    return _cache["items"]

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

async def run_remote(job: dict, url: str, name: str):
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
        await push_to_hf(tmp, fname, "URL import")
        job.update(stage="done", **links(fname))
        log.info("URL import OK: %s (%.1f MB)", fname, job["done"] / 1048576)
    except Exception as e:
        log.error("URL import failed: %s", e)
        job.update(stage="error", error=str(e) or type(e).__name__)
    finally:
        if tmp:
            Path(tmp).unlink(missing_ok=True)

# ───────────────────────── Subtitle soft-mux (mkvmerge) ─────────────────────────
MUX_SEM = asyncio.Semaphore(1)  # one merge at a time (disk + CPU)

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

async def fetch_source(job: dict, src: dict, dest_stem: Path, label: str, default_ext: str):
    """Download a storage file or a public URL to disk. Returns (path, original_name)."""
    if src["type"] == "storage":
        name = safe_name(src["value"])
        url, public = hf_url(name), False
        auth = {"Authorization": f"Bearer {HF_TOKEN}"} if HF_TOKEN else None
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
            job.update(label="Saving to storage…", pct=None)
            await push_to_hf(out, out_name, "Subtitle mux")
        job.update(stage="done", label=None, **links(out_name))
        log.info("Subtitle mux OK: %s", out_name)
    except Exception as e:
        log.error("Subtitle mux failed: %s", e)
        job.update(stage="error", error=str(e) or type(e).__name__)
    finally:
        if work:
            shutil.rmtree(work, ignore_errors=True)

def mp4_name(name: str) -> str:
    name = Path(name.replace("\\", "/")).name.strip() or "output"
    if name.lower().endswith(".mp4"):
        return name
    if Path(name).suffix.lower() in (VIDEO_EXT | {".avi"}):
        return str(Path(name).with_suffix(".mp4"))
    return name + ".mp4"

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
            job.update(label="Saving to storage…", pct=None)
            await push_to_hf(out, out_name, "Hardsub")
        job.update(stage="done", label=None, **links(out_name))
        log.info("Hardsub OK: %s", out_name)
    except Exception as e:
        log.error("Hardsub failed: %s", e)
        job.update(stage="error", error=str(e) or type(e).__name__)
    finally:
        if work:
            shutil.rmtree(work, ignore_errors=True)

# ───────────────────────── Zip handler ─────────────────────────
# Two phases: (1) STAGE the zip on disk and list its contents, nothing goes to storage;
# (2) COMMIT an action chosen by the user. Unused stages are deleted after 45 minutes.
STAGE_ROOT = Path(os.getenv("STAGE_DIR", "/tmp/mycloud-stages"))
STAGES: dict = {}
STAGE_TTL = 45 * 60
SUB_EXT = {".srt", ".ass", ".ssa", ".vtt"}
VID_EXT = VIDEO_EXT | {".avi"}

def zip_entries(path) -> list:
    try:
        with zipfile.ZipFile(path) as zf:
            infos = [i for i in zf.infolist() if not i.is_dir() and not i.filename.startswith("__MACOSX/")
                     and Path(i.filename).name not in {".DS_Store", "Thumbs.db"}]
    except zipfile.BadZipFile:
        raise ValueError("That file is not a valid zip archive")
    if not infos:
        raise ValueError("The zip is empty")
    if len(infos) > 5000:
        raise ValueError("The zip has too many files (limit 5000)")
    if sum(i.file_size for i in infos) > MAX_FILE_SIZE:
        raise ValueError("The zip is larger than the size limit once extracted")
    def kind(n):
        e = Path(n).suffix.lower()
        return "video" if e in VID_EXT else "sub" if e in SUB_EXT else "other"
    return [{"path": i.filename, "size": i.file_size, "enc": bool(i.flag_bits & 1), "kind": kind(i.filename)} for i in infos]

def clean_name(n: str, i: int = 0) -> str:
    try:
        return safe_name(Path(n.replace("\\", "/")).name)
    except HTTPException:
        return f"file_{i}"

def unique_name(name: str, taken: set) -> str:
    stem, suf, cand, k = Path(name).stem, Path(name).suffix, name, 1
    while cand in taken:
        k += 1
        cand = f"{stem} ({k}){suf}"
    taken.add(cand)
    return cand

def extract_entries(zip_path, names, work: Path, job: dict) -> dict:
    """Extract only the chosen entries (never extractall: no path traversal, no zip bombs)."""
    out_paths, done = {}, 0
    with zipfile.ZipFile(zip_path) as zf:
        infos = {i.filename: i for i in zf.infolist()}
        total = sum(infos[n].file_size for n in names) or 1
        for n in names:
            info = infos[n]
            if info.flag_bits & 1:
                raise ValueError(f"{n} is password-protected; protected zips are not supported")
            dest = work / f"{len(out_paths):04d}{_ext(n, '.bin')}"
            with zf.open(info) as src, open(dest, "wb") as out:
                while chunk := src.read(1024 * 1024):
                    done += len(chunk)
                    if done > MAX_FILE_SIZE:
                        raise ValueError("Extracted data is larger than the size limit")
                    out.write(chunk)
                    job.update(label=f"Extracting · {done * 100 // total}%", pct=done * 100 // total)
            out_paths[n] = dest
    return out_paths

async def push_many(pairs, note: str):
    """One commit for many files (much faster than one commit per file)."""
    ops = [CommitOperationAdd(path_in_repo=n, path_or_fileobj=str(p)) for p, n in pairs]
    await asyncio.to_thread(hf_api.create_commit, repo_id=HF_REPO, repo_type="dataset", operations=ops,
                            commit_message=f"{note}: {len(ops)} file(s)")
    _cache["t"] = 0

async def mkvmerge_run(job, vpath, spath, out, lang, track, label):
    cmd = ["mkvmerge", "-o", str(out), str(vpath), "--language", f"0:{lang}", "--track-name", f"0:{track}"]
    if Path(spath).suffix.lower() in {".srt", ".ass", ".ssa"}:
        cmd += ["--sub-charset", "0:UTF-8"]
    cmd.append(str(spath))
    job.update(label=label, pct=0)
    proc = await asyncio.create_subprocess_exec(*cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT)
    tail = b""
    while chunk := await proc.stdout.read(4096):
        tail = (tail + chunk)[-3000:]
        m = re.findall(rb"Progress: (\d+)%", tail)
        if m:
            job.update(label=label, pct=int(m[-1]))
    rc = await proc.wait()
    if rc >= 2 or not Path(out).exists():
        msg = re.sub(r"Progress: \d+%\s*", "", tail.decode("utf-8", "replace")).strip()[-300:]
        raise ValueError("mkvmerge failed: " + msg)

def drop_stage(sid: str):
    st = STAGES.pop(sid, None)
    if st:
        shutil.rmtree(st["dir"], ignore_errors=True)

async def stage_janitor():
    while True:
        await asyncio.sleep(300)
        for sid, st in list(STAGES.items()):
            if not st["busy"] and time.time() - st["ts"] > STAGE_TTL:
                drop_stage(sid)

async def finish_stage(sid: str, d: Path, path: Path, name: str) -> dict:
    try:
        entries = await asyncio.to_thread(zip_entries, path)
    except Exception:
        shutil.rmtree(d, ignore_errors=True)
        raise
    STAGES[sid] = {"dir": d, "path": path, "name": name, "entries": entries, "ts": time.time(), "busy": False}
    return {"id": sid, "name": name, "size": path.stat().st_size, "entries": entries}

async def run_stage_url(job: dict, src: dict):
    d = None
    try:
        job.update(stage="working")
        sid = uuid.uuid4().hex[:12]
        d = STAGE_ROOT / sid
        d.mkdir(parents=True, exist_ok=True)
        path, name = await fetch_source(job, src, d / "archive", "zip", ".zip")
        job.update(label="Reading contents…", pct=None)
        name = clean_name(name)
        job["result"] = await finish_stage(sid, d, path, name)
        job.update(stage="done", label=None, name=name)
    except Exception as e:
        if d:
            shutil.rmtree(d, ignore_errors=True)
        job.update(stage="error", error=str(e) or type(e).__name__)

async def run_zip_commit(job, sid, st, mode, files, pairs, lang, track, zip_name):
    st["busy"], work = True, None
    try:
        if mode == "extract_sub" and any(p["sub"] for p in pairs) and not shutil.which("mkvmerge"):
            raise ValueError("mkvmerge is not installed on the server (install the mkvtoolnix package)")
        job.update(stage="working", label="Waiting for another job to finish", pct=None)
        async with MUX_SEM:
            _cache["t"] = 0
            taken = {f["name"] for f in await list_files()}
            work = st["dir"] / f"work_{job['id']}"
            work.mkdir(exist_ok=True)
            outputs = []
            if mode == "zip":
                nm = clean_name(zip_name or st["name"])
                outputs.append((st["path"], unique_name(nm if nm.lower().endswith(".zip") else nm + ".zip", taken)))
            else:
                need = list(dict.fromkeys(files + [p["video"] for p in pairs] + [p["sub"] for p in pairs if p["sub"]]))
                paths = await asyncio.to_thread(extract_entries, st["path"], need, work, job)
                for i, n in enumerate(files):
                    outputs.append((paths[n], unique_name(clean_name(n, i), taken)))
                for i, p in enumerate(pairs):
                    if p["sub"]:
                        out = work / f"mux_{i}.mkv"
                        await mkvmerge_run(job, paths[p["video"]], paths[p["sub"]], out, lang, track,
                                           f"Adding subtitles {i + 1}/{len(pairs)}")
                        outputs.append((out, unique_name(Path(clean_name(p["video"], i)).stem + ".mkv", taken)))
                    else:
                        outputs.append((paths[p["video"]], unique_name(clean_name(p["video"], i), taken)))
            job.update(label=f"Saving {len(outputs)} file(s) to storage…", pct=None)
            await push_many(outputs, "Zip import")
            saved = [{"name": n, "size": Path(p).stat().st_size, **links(n)} for p, n in outputs]
        job.update(stage="done", label=None, name=f"{len(saved)} file(s)", result={"files": saved})
        drop_stage(sid)
        log.info("Zip commit OK (%s): %d file(s)", mode, len(saved))
    except Exception as e:
        log.error("Zip commit failed: %s", e)
        st["busy"] = False
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
    shutil.rmtree(STAGE_ROOT, ignore_errors=True)
    STAGE_ROOT.mkdir(parents=True, exist_ok=True)
    asyncio.create_task(stage_janitor())
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
:root{--bg:#e9edf1;--card:#fff;--ink:#101b2b;--mute:#5b6b7f;--line:#d5dce4;--acc:#2f5bff;--acc-ink:#fff;--ok:#12813f;--bad:#c62828;--field:#f5f7fa}
@media(prefers-color-scheme:dark){:root{--bg:#0d141d;--card:#141d29;--ink:#e8edf3;--mute:#93a1b3;--line:#263344;--acc:#6f8cff;--acc-ink:#0d141d;--ok:#4cc37f;--bad:#ff7b7b;--field:#0f1722}}
*{box-sizing:border-box;margin:0}
body{font-family:'Onest',system-ui,-apple-system,'Segoe UI',sans-serif;background:var(--bg);color:var(--ink);line-height:1.5;-webkit-font-smoothing:antialiased}
button,input,textarea{font:inherit;color:inherit}
:focus-visible{outline:2px solid var(--acc);outline-offset:2px}
.btn{background:var(--acc);color:var(--acc-ink);border:0;border-radius:8px;padding:10px 16px;font-weight:600;cursor:pointer}
.btn:disabled{opacity:.5;cursor:default}
.btn.ghost{background:transparent;color:var(--ink);border:1px solid var(--line)}
.btn.sm{padding:6px 10px;font-size:.82rem;font-weight:500}
input[type=text],input[type=password],textarea{width:100%;background:var(--field);border:1px solid var(--line);border-radius:8px;padding:10px 12px}
"""

FONT = '<link rel="preconnect" href="https://fonts.googleapis.com"><link href="https://fonts.googleapis.com/css2?family=Onest:wght@400;500;600;800&display=swap" rel="stylesheet">'

LOGIN_HTML = """<!DOCTYPE html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Sign in · My Cloud</title>""" + FONT + "<style>" + BASE_CSS + """
body{min-height:100vh;display:grid;place-items:center;padding:20px}
form{width:100%;max-width:380px;background:var(--card);border:1px solid var(--line);border-radius:14px;padding:32px}
h1{font-size:1.6rem;font-weight:800;letter-spacing:-.02em;margin-bottom:4px}
p.s{color:var(--mute);margin-bottom:24px}label{display:block;font-size:.85rem;color:var(--mute);margin:14px 0 6px}
.btn{width:100%;margin-top:22px}.err{background:color-mix(in srgb,var(--bad) 12%,transparent);color:var(--bad);padding:10px 12px;border-radius:8px;margin-bottom:8px;font-size:.9rem}
</style></head><body><form method="post" action="/login"><h1>My Cloud</h1><p class="s">Sign in to upload and manage files.</p>
%%ERROR%%<input type="hidden" name="next" value="%%NEXT%%">
<label for="u">Username</label><input id="u" name="username" type="text" autocomplete="username" required>
<label for="p">Password</label><input id="p" name="password" type="password" autocomplete="current-password" required>
<button class="btn" type="submit">Sign in</button></form></body></html>"""

DASHBOARD_HTML = """<!DOCTYPE html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>My Cloud</title>""" + FONT + "<style>" + BASE_CSS + """
header{display:flex;justify-content:space-between;align-items:center;padding:18px clamp(16px,4vw,40px)}
.logo{font-weight:800;font-size:1.15rem;letter-spacing:-.02em}
main{max-width:920px;margin:0 auto;padding:8px clamp(16px,4vw,40px) 80px}
h1{font-size:clamp(2rem,5vw,3rem);font-weight:800;letter-spacing:-.035em;line-height:1.05;margin:18px 0 6px}
.lead{color:var(--mute);margin-bottom:26px;max-width:52ch}
.panel{background:var(--card);border:1px solid var(--line);border-radius:14px}
.tabs{display:flex;border-bottom:1px solid var(--line)}
.tab{flex:1;padding:14px;background:none;border:0;cursor:pointer;color:var(--mute);font-weight:600;border-bottom:2px solid transparent;margin-bottom:-1px}
.tab[aria-selected=true]{color:var(--ink);border-bottom-color:var(--acc)}
.pane{padding:22px}.pane[hidden]{display:none}
.drop{display:block;border:2px dashed var(--line);border-radius:12px;padding:44px 20px;text-align:center;cursor:pointer;transition:border-color .15s,background .15s}
.drop:hover,.drop.over{border-color:var(--acc);background:color-mix(in srgb,var(--acc) 6%,transparent)}
.drop b{display:block;font-size:1.15rem;margin-bottom:4px}.drop span{color:var(--mute);font-size:.9rem}
.row{display:flex;gap:10px;margin-top:12px;flex-wrap:wrap}.row input{flex:1;min-width:180px}
textarea{min-height:96px;resize:vertical}
.hint{color:var(--mute);font-size:.85rem;margin-top:8px}
.xfers{margin-top:14px;display:grid;gap:10px}
.x{border:1px solid var(--line);border-radius:10px;padding:12px 14px;background:var(--field)}
.x .top{display:flex;justify-content:space-between;gap:12px;font-size:.9rem}.x .n{font-weight:600;word-break:break-all}
.x .st{color:var(--mute);white-space:nowrap;font-variant-numeric:tabular-nums}.x.error .st{color:var(--bad)}.x.done .st{color:var(--ok)}
.bar{height:6px;background:var(--line);border-radius:3px;margin-top:10px;overflow:hidden;position:relative}
.bar i{position:absolute;inset:0 auto 0 0;width:0;background:var(--acc);border-radius:3px;transition:width .2s}
.bar.ind i{width:35%;animation:slide 1.1s ease-in-out infinite}
@keyframes slide{from{left:-35%}to{left:100%}}
@media(prefers-reduced-motion:reduce){.bar.ind i{animation:none;width:100%;opacity:.5}}
.files{margin-top:36px}.fh{display:flex;justify-content:space-between;align-items:baseline;gap:12px;margin-bottom:12px;flex-wrap:wrap}
.fh h2{font-size:1.2rem;font-weight:800;letter-spacing:-.02em}.fh input{max-width:240px}
.f{display:flex;align-items:center;gap:12px;padding:12px 16px;border-bottom:1px solid var(--line);flex-wrap:wrap}
.f:last-child{border:0}.f .n{flex:1;min-width:200px;word-break:break-all;font-weight:500}.f .sz{color:var(--mute);font-size:.85rem;font-variant-numeric:tabular-nums;min-width:70px;text-align:right}
.f .a{display:flex;gap:6px;flex-wrap:wrap}.empty{padding:32px;text-align:center;color:var(--mute)}
dialog{border:0;border-radius:14px;padding:0;background:#000;max-width:min(92vw,960px);width:100%}dialog::backdrop{background:rgba(0,0,0,.7)}
dialog video{display:block;width:100%;max-height:80vh}dialog form{position:absolute;top:8px;right:8px}
#toast{position:fixed;bottom:20px;left:50%;transform:translateX(-50%);background:var(--ink);color:var(--bg);padding:10px 16px;border-radius:8px;font-size:.9rem;opacity:0;pointer-events:none;transition:opacity .2s}
#toast.on{opacity:1}
.steps{display:grid;gap:14px}
.src{border:1px solid var(--line);border-radius:12px;padding:14px;min-width:0}
.src legend{padding:0 6px;font-weight:700;font-size:.9rem}
.seg{display:inline-flex;border:1px solid var(--line);border-radius:8px;overflow:hidden;margin-bottom:10px}
.seg button{background:none;border:0;padding:6px 12px;cursor:pointer;color:var(--mute);font-size:.85rem}
.seg button[aria-pressed=true]{background:var(--acc);color:var(--acc-ink)}
.pk{position:relative}
.pk-list{position:absolute;left:0;right:0;top:calc(100% + 4px);max-height:240px;overflow:auto;background:var(--card);border:1px solid var(--line);border-radius:10px;z-index:5;box-shadow:0 8px 24px rgba(0,0,0,.18)}
.pk-list div{padding:8px 12px;cursor:pointer;word-break:break-all;display:flex;justify-content:space-between;gap:10px;font-size:.9rem}
.pk-list div:hover{background:color-mix(in srgb,var(--acc) 10%,transparent)}
.pk-list small{color:var(--mute);white-space:nowrap}.pk-list .none{color:var(--mute);cursor:default}
.grid3{display:grid;grid-template-columns:2fr 1fr 2fr;gap:10px}
.tabs{overflow-x:auto}.tab{white-space:nowrap;padding:14px 16px;flex:1 0 auto}
select{width:100%;background:var(--field);border:1px solid var(--line);border-radius:8px;padding:10px 12px}
.gridE{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:10px}
[hidden]{display:none!important}
.zl{max-height:320px;overflow:auto;border:1px solid var(--line);border-radius:10px}
.zr{display:flex;align-items:center;gap:10px;padding:8px 12px;border-bottom:1px solid var(--line);cursor:pointer;font-size:.9rem}
.zr:last-child{border:0}.zr input{accent-color:var(--acc);width:16px;height:16px;flex:none}
.zn{flex:1;min-width:0;word-break:break-all}.zr small{color:var(--mute);min-width:64px;text-align:right}
.bd{font-size:.72rem;padding:2px 8px;border-radius:99px;border:1px solid var(--line);color:var(--mute);white-space:nowrap}
.bd.video{color:var(--acc);border-color:var(--acc)}.bd.sub{color:var(--ok);border-color:var(--ok)}
.note{background:color-mix(in srgb,#e8a100 14%,transparent);border:1px solid color-mix(in srgb,#e8a100 45%,transparent);border-radius:10px;padding:10px 12px;font-size:.88rem}
.modes{display:grid;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));gap:10px}
.modes button{text-align:left;background:var(--field);border:1px solid var(--line);border-radius:10px;padding:12px;cursor:pointer}
.modes button[aria-pressed=true]{border-color:var(--acc);box-shadow:0 0 0 2px color-mix(in srgb,var(--acc) 25%,transparent)}
.modes b{display:block}.modes span{color:var(--mute);font-size:.82rem}
.pr{display:grid;grid-template-columns:1fr 1fr;gap:10px;align-items:center;padding:6px 0;border-bottom:1px solid var(--line)}
@media(max-width:700px){.pr{grid-template-columns:1fr}}
.gridE label,.grid3 label{font-size:.8rem;color:var(--mute);display:block;margin-bottom:4px}
@media(max-width:700px){.grid3{grid-template-columns:1fr}}
</style></head><body>
<header><div class="logo">My Cloud</div><div><span id="who" style="color:var(--mute);margin-right:10px"></span><form id="lo" method="post" action="/logout" style="display:inline"><button class="btn ghost sm">Sign out</button></form></div></header>
<main>
<h1>Put a file online.</h1>
<p class="lead">Upload from this device or paste a link. You get a download link and a streaming link that plays in a browser or video player.</p>
<div class="panel">
 <div class="tabs" role="tablist">
  <button class="tab" role="tab" id="t1" aria-selected="true" aria-controls="p1">From this device</button>
  <button class="tab" role="tab" id="t2" aria-selected="false" aria-controls="p2">From a link</button>
  <button class="tab" role="tab" id="t3" aria-selected="false" aria-controls="p3">Add subtitles</button>
  <button class="tab" role="tab" id="t4" aria-selected="false" aria-controls="p4">Hardcode subtitles</button>
  <button class="tab" role="tab" id="t5" aria-selected="false" aria-controls="p5">Zip handler</button>
 </div>
 <div class="pane" id="p1" role="tabpanel">
  <input type="text" id="dname" placeholder="Save as (optional, single file only)" aria-label="File name" style="margin-bottom:12px">
  <label class="drop" id="drop" for="pick"><b>Drop files here or choose them</b><span>Up to 20&nbsp;GB each. Videos work best as MP4.</span></label>
  <input type="file" id="pick" multiple hidden>
 </div>
 <div class="pane" id="p2" role="tabpanel" hidden>
  <textarea id="urls" placeholder="https://example.com/video.mp4&#10;One link per line" aria-label="File links"></textarea>
  <div class="row"><input type="text" id="rname" placeholder="Save as (optional, single link only)" aria-label="File name"><button class="btn" id="fetch">Fetch to cloud</button></div>
  <p class="hint">The server downloads the file directly, so nothing passes through your device.</p>
 </div>
 <div class="pane" id="p3" role="tabpanel" hidden><div class="steps">
   <fieldset class="src" id="srcV"><legend>Video</legend>
    <div class="seg"><button type="button" data-m="storage" aria-pressed="true">From storage</button><button type="button" data-m="url" aria-pressed="false">From link</button></div>
    <div class="pk"><input type="text" class="pk-in" role="combobox" aria-expanded="false" autocomplete="off" placeholder="Search your videos" aria-label="Search your videos"><div class="pk-list" role="listbox" hidden></div></div>
    <input type="text" class="u-in" placeholder="https://…/movie.mkv" aria-label="Video link" hidden>
   </fieldset>
   <fieldset class="src" id="srcS"><legend>Subtitle (.srt, .ass, .ssa, .vtt)</legend>
    <div class="seg"><button type="button" data-m="storage" aria-pressed="true">From storage</button><button type="button" data-m="url" aria-pressed="false">From link</button></div>
    <div class="pk"><input type="text" class="pk-in" role="combobox" aria-expanded="false" autocomplete="off" placeholder="Search your subtitle files" aria-label="Search your subtitle files"><div class="pk-list" role="listbox" hidden></div></div>
    <input type="text" class="u-in" placeholder="https://…/movie.srt" aria-label="Subtitle (.srt, .ass, .ssa, .vtt) link" hidden>
   </fieldset>
   <div class="grid3"><div><label for="oname">Save as</label><input type="text" id="oname" placeholder="movie_sub.mkv"></div><div><label for="lang">Language code</label><input type="text" id="lang" value="si"></div><div><label for="tname">Track name</label><input type="text" id="tname" value="සිංහල | Sinhala"></div></div>
   <div><button class="btn" id="mux">Merge subtitles &amp; save</button></div>
   <p class="hint" style="margin:0">Adds the subtitle as a selectable track (soft-sub). The video is not re-encoded, so it stays fast. Output is .mkv. Needs free disk for the video twice.</p>
  </div></div>
 <div class="pane" id="p4" role="tabpanel" hidden><div class="steps">
   <fieldset class="src" id="hsrcV"><legend>Video</legend>
    <div class="seg"><button type="button" data-m="storage" aria-pressed="true">From storage</button><button type="button" data-m="url" aria-pressed="false">From link</button></div>
    <div class="pk"><input type="text" class="pk-in" role="combobox" aria-expanded="false" autocomplete="off" placeholder="Search your videos" aria-label="Search your videos"><div class="pk-list" role="listbox" hidden></div></div>
    <input type="text" class="u-in" placeholder="https://…/movie.mkv" aria-label="Video link" hidden>
   </fieldset>
   <fieldset class="src" id="hsrcS"><legend>Subtitle (.srt, .ass, .ssa, .vtt)</legend>
    <div class="seg"><button type="button" data-m="storage" aria-pressed="true">From storage</button><button type="button" data-m="url" aria-pressed="false">From link</button></div>
    <div class="pk"><input type="text" class="pk-in" role="combobox" aria-expanded="false" autocomplete="off" placeholder="Search your subtitle files" aria-label="Search your subtitle files"><div class="pk-list" role="listbox" hidden></div></div>
    <input type="text" class="u-in" placeholder="https://…/movie.srt" aria-label="Subtitle (.srt, .ass, .ssa, .vtt) link" hidden>
   </fieldset>
   <div class="gridE"><div><label for="hname">Save as</label><input type="text" id="hname" placeholder="movie_hardsub.mp4"></div><div><label for="hfont">Font</label><input type="text" id="hfont" value="Noto Sans Sinhala"></div></div>
   <div class="gridE"><div><label for="hsize">Font size</label><input type="text" id="hsize" value="22" inputmode="numeric"></div>
    <div><label for="hcrf">Quality</label><select id="hcrf"><option value="18">High (larger file)</option><option value="21" selected>Balanced</option><option value="25">Smaller file</option></select></div>
    <div><label for="hpre">Speed</label><select id="hpre"><option value="ultrafast">Fastest (bigger file)</option><option value="veryfast" selected>Fast</option><option value="medium">Slow (smaller file)</option></select></div></div>
   <div><button class="btn" id="burn">Burn subtitles &amp; save</button></div>
   <p class="hint" style="margin:0">Draws the subtitle into the picture, so it shows in every player. This re-encodes the video (H.264 + AAC, output .mp4) and can take a long time on a shared CPU.</p>
  </div></div>
 <div class="pane" id="p5" role="tabpanel" hidden><div class="steps">
  <div id="zin" class="steps">
   <label class="drop" id="zdrop" for="zpick"><b>Drop a .zip here or choose one</b><span>Nothing is saved until you pick an action.</span></label><input type="file" id="zpick" accept=".zip,application/zip" hidden>
   <fieldset class="src" id="zsrc"><legend>Or open a zip from storage or a link</legend>
    <div class="seg"><button type="button" data-m="storage" aria-pressed="true">From storage</button><button type="button" data-m="url" aria-pressed="false">From link</button></div>
    <div class="pk"><input type="text" class="pk-in" role="combobox" aria-expanded="false" autocomplete="off" placeholder="Search your zip files" aria-label="Search zip files"><div class="pk-list" role="listbox" hidden></div></div>
    <input type="text" class="u-in" placeholder="https://…/files.zip" aria-label="Zip link" hidden>
    <div style="margin-top:12px"><button class="btn" id="zload" type="button">Open zip</button></div>
   </fieldset>
  </div>
  <div id="zstage" class="steps" hidden>
   <div class="note" role="status"><b>Not saved yet.</b> Choose what to do with this zip below. If you leave without saving, nothing is added to your storage.</div>
   <div class="fh" style="margin:0"><strong id="zhead"></strong><span><button class="btn ghost sm" id="zall" type="button">Select all</button> <button class="btn ghost sm" id="znone" type="button">Select none</button> <button class="btn ghost sm" id="zdiscard" type="button">Discard</button></span></div>
   <input type="text" id="zq" placeholder="Search inside the zip" aria-label="Search inside the zip">
   <div class="zl" id="zlist"></div>
   <div class="modes" id="zmodes" role="group" aria-label="What to do with this zip">
    <button type="button" data-m="zip" aria-pressed="false"><b>Save as ZIP</b><span>Keep the archive as one file.</span></button>
    <button type="button" data-m="extract" aria-pressed="true"><b>Extract &amp; save</b><span>Save the selected files one by one.</span></button>
    <button type="button" data-m="extract_sub" aria-pressed="false"><b>Extract + soft subtitles</b><span>Add subtitles to videos, then save.</span></button>
   </div>
   <div id="zm-zip" hidden><div class="gridE"><div><label for="zout">Save as</label><input type="text" id="zout"></div></div></div>
   <div id="zm-extract" class="hint" style="margin:0"></div>
   <div id="zm-sub" hidden><div id="zpairs"></div><div class="gridE" style="margin-top:10px"><div><label for="zlang">Language code</label><input type="text" id="zlang" value="si"></div><div><label for="ztrack">Track name</label><input type="text" id="ztrack" value="සිංහල | Sinhala"></div></div></div>
   <div><button class="btn" id="zsave" type="button">Save to storage</button></div>
  </div>
  <div id="zres" class="zl" hidden></div>
 </div></div>
 <div class="xfers" id="xfers" style="padding:0 22px 22px;margin:0"></div>
</div>
<section class="files"><div class="fh"><h2>Your files <span id="cnt" style="color:var(--mute);font-weight:500"></span></h2><input type="text" id="q" placeholder="Search files" aria-label="Search files"></div>
<div class="panel" id="list"><div class="empty">Loading…</div></div></section>
</main>
<dialog id="dlg"><form method="dialog"><button class="btn sm">Close</button></form><video id="vid" controls playsinline></video></dialog>
<div id="toast" role="status"></div>
<script>
const $=id=>document.getElementById(id);let FILES=[];
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmt=b=>b<1024?b+' B':b<1048576?(b/1024).toFixed(1)+' KB':b<1073741824?(b/1048576).toFixed(1)+' MB':(b/1073741824).toFixed(2)+' GB';
const isVid=n=>/\\.(mp4|webm|mov|m4v|mkv|ogv)$/i.test(n);
function toast(m){const t=$('toast');t.textContent=m;t.classList.add('on');clearTimeout(t._h);t._h=setTimeout(()=>t.classList.remove('on'),1800)}
async function api(u,o){const r=await fetch(u,Object.assign({credentials:'same-origin'},o));if(r.status===401){location.href='/login?next=%2F';throw 0}return r}
function copy(t){navigator.clipboard.writeText(t).then(()=>toast('Link copied'),()=>toast('Copy failed'))}
document.querySelectorAll('.tab').forEach(t=>t.onclick=()=>{document.querySelectorAll('.tab').forEach(x=>{x.setAttribute('aria-selected',x===t);$(x.getAttribute('aria-controls')).hidden=x!==t})});
function xfer(name){const d=document.createElement('div');d.className='x';d.innerHTML='<div class="top"><span class="n"></span><span class="st">Starting</span></div><div class="bar"><i></i></div>';d.querySelector('.n').textContent=name;$('xfers').prepend(d);
 return{set(st,p,ind){d.querySelector('.st').textContent=st;const b=d.querySelector('.bar');b.classList.toggle('ind',!!ind);if(p!=null)b.firstChild.style.width=p+'%'},end(cls,st){d.className='x '+cls;d.querySelector('.st').textContent=st;d.querySelector('.bar').style.display='none';setTimeout(()=>d.remove(),cls==='done'?6000:20000)}}}
function upload(file,name){name=name||file.name;const x=xfer(name),t0=Date.now();const r=new XMLHttpRequest();
 r.open('POST','/api/upload?name='+encodeURIComponent(name));
 r.upload.onprogress=e=>{if(!e.lengthComputable)return;const p=e.loaded/e.total*100,s=e.loaded/((Date.now()-t0)/1000||1);x.set(p<100?Math.round(p)+'% · '+fmt(s)+'/s':'Saving to storage…',p,p>=100)};
 r.onload=()=>{if(r.status===200){x.end('done','Done');toast('Uploaded '+file.name);load()}else if(r.status===401)location.href='/login';else{let m='Upload failed';try{m=JSON.parse(r.responseText).detail||m}catch(e){}x.end('error',m)}};
 r.onerror=()=>x.end('error','Network error');r.send(file)}
const drop=$('drop');['dragover','dragenter'].forEach(e=>drop.addEventListener(e,ev=>{ev.preventDefault();drop.classList.add('over')}));
['dragleave','drop'].forEach(e=>drop.addEventListener(e,ev=>{ev.preventDefault();drop.classList.remove('over')}));
function many(fs){fs=[...fs];let n=$('dname').value.trim();fs.forEach(f=>{let nm='';if(fs.length===1&&n){const i=f.name.lastIndexOf('.');nm=n.includes('.')||i<0?n:n+f.name.slice(i)}upload(f,nm)});$('dname').value=''}
drop.addEventListener('drop',e=>many(e.dataTransfer.files));$('pick').onchange=e=>{many(e.target.files);e.target.value=''};
$('fetch').onclick=async()=>{const urls=$('urls').value.split(/\\s+/).filter(Boolean);if(!urls.length)return toast('Paste at least one link');
 const name=urls.length===1?$('rname').value.trim():'';$('fetch').disabled=true;
 for(const url of urls){const x=xfer(url.split('/').pop()||url);
  try{const r=await api('/api/remote',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({url,name})});const j=await r.json();
   if(!r.ok){x.end('error',j.detail||'Rejected');continue}poll(j.id,x)}catch(e){x.end('error','Request failed')}}
 $('urls').value='';$('rname').value='';$('fetch').disabled=false};
async function poll(id,x,cb){const r=await api('/api/jobs/'+id);const j=await r.json();
 if(j.label&&j.stage!=='done'&&j.stage!=='error')x.set(j.label,j.pct,j.pct==null);
 else if(j.stage==='downloading')x.set('Downloading '+(j.total?Math.round(j.done/j.total*100)+'% · ':'')+fmt(j.speed)+'/s',j.total?j.done/j.total*100:null,!j.total);
 else if(j.stage==='uploading')x.set('Saving to storage…',100,true);
 else if(j.stage==='done'){x.end('done','Done');if(cb)cb(j);else{toast('Saved '+j.name);load()}return}
 else if(j.stage==='error'){x.end('error',j.error||'Failed');return}
 setTimeout(()=>poll(id,x,cb),700)}
function render(){const q=$('q').value.toLowerCase(),L=FILES.filter(f=>f.name.toLowerCase().includes(q));$('cnt').textContent=FILES.length?'('+FILES.length+')':'';
 if(!L.length){$('list').innerHTML='<div class="empty">'+(FILES.length?'No files match.':'Nothing here yet. Upload a file to get its link.')+'</div>';return}
 $('list').innerHTML=L.map((f,i)=>'<div class="f"><span class="n">'+esc(f.name)+'</span><span class="sz">'+fmt(f.size)+'</span><span class="a">'+(isVid(f.name)?'<button class="btn sm" data-a="play" data-i="'+i+'">Play</button>':'')+'<button class="btn ghost sm" data-a="cdn" data-i="'+i+'">Copy stream link</button><button class="btn ghost sm" data-a="dl" data-i="'+i+'">Copy download link</button><button class="btn ghost sm" data-a="del" data-i="'+i+'">Delete</button></span></div>').join('');
 $('list')._L=L}
$('list').onclick=async e=>{const b=e.target.closest('button');if(!b)return;const f=$('list')._L[+b.dataset.i],a=b.dataset.a;
 if(a==='cdn')copy(f.cdn_url);else if(a==='dl')copy(f.download_url);
 else if(a==='play'){$('vid').src=f.cdn_url;$('dlg').showModal();$('vid').play().catch(()=>{})}
 else if(a==='del'&&confirm('Delete '+f.name+'? This cannot be undone.')){const r=await api('/api/files/'+encodeURIComponent(f.name),{method:'DELETE'});if(r.ok){toast('Deleted');load()}else toast('Delete failed')}};
$('dlg').addEventListener('close',()=>{$('vid').pause();$('vid').removeAttribute('src');$('vid').load()});$('q').oninput=render;
async function load(){try{const r=await api('/api/files');const j=await r.json();FILES=j.items||[];if(j.error)toast(j.error);render()}catch(e){}}
const SUBX=['srt','ass','ssa','vtt'],VIDX=['mkv','mp4','m4v','mov','webm','avi','ogv'];
const ext=n=>{const i=n.lastIndexOf('.');return i<0?'':n.slice(i+1).toLowerCase()};
function mkSrc(root,exts,onPick){let mode='storage',sel=null;const inp=root.querySelector('.pk-in'),lst=root.querySelector('.pk-list'),uin=root.querySelector('.u-in'),box=root.querySelector('.pk');
 function show(){const q=inp.value.toLowerCase(),L=FILES.filter(f=>exts.includes(ext(f.name))&&f.name.toLowerCase().includes(q)).slice(0,60);
  lst.innerHTML=L.length?L.map((f,i)=>'<div role="option" data-i="'+i+'"><span>'+esc(f.name)+'</span><small>'+fmt(f.size)+'</small></div>').join(''):'<div class="none">No matching files in storage</div>';lst._L=L;lst.hidden=false;inp.setAttribute('aria-expanded','true')}
 function hide(){lst.hidden=true;inp.setAttribute('aria-expanded','false')}
 function pick(f){sel=f.name;inp.value=f.name;hide();if(onPick)onPick(f.name)}
 inp.addEventListener('focus',show);inp.addEventListener('blur',hide);inp.addEventListener('input',()=>{sel=null;show()});
 inp.addEventListener('keydown',e=>{if(e.key==='Escape')hide();if(e.key==='Enter'&&!lst.hidden&&(lst._L||[]).length){e.preventDefault();pick(lst._L[0])}});
 lst.addEventListener('mousedown',e=>{const d=e.target.closest('[data-i]');if(d){e.preventDefault();pick(lst._L[+d.dataset.i])}});
 root.querySelectorAll('.seg button').forEach(b=>b.onclick=()=>{mode=b.dataset.m;root.querySelectorAll('.seg button').forEach(x=>x.setAttribute('aria-pressed',x===b));box.hidden=mode!=='storage';uin.hidden=mode!=='url'});
 return{get(){if(mode==='url'){const v=uin.value.trim();return v?{type:'url',value:v}:null}const n=sel||(FILES.find(f=>f.name===inp.value)||{}).name;return n?{type:'storage',value:n}:null}}}
const vs=mkSrc($('srcV'),VIDX,n=>{const o=$('oname');if(!o._m){const i=n.lastIndexOf('.');o.value=(i>0?n.slice(0,i):n)+'_sub.mkv'}}),ss=mkSrc($('srcS'),SUBX);
$('oname').addEventListener('input',e=>{e.target._m=!!e.target.value});
$('mux').onclick=async()=>{const v=vs.get(),s=ss.get();if(!v)return toast('Choose a video');if(!s)return toast('Choose a subtitle file');
 const name=$('oname').value.trim();$('mux').disabled=true;const x=xfer(name||v.value.split('/').pop());
 try{const r=await api('/api/subtitle',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({video:v,sub:s,name:name,lang:$('lang').value.trim()||'si',track:$('tname').value.trim()})});const j=await r.json();
  if(!r.ok)x.end('error',j.detail||'Rejected');else poll(j.id,x)}catch(e){x.end('error','Request failed')}
 $('mux').disabled=false};
const hv=mkSrc($('hsrcV'),VIDX,n=>{const o=$('hname');if(!o._m){const i=n.lastIndexOf('.');o.value=(i>0?n.slice(0,i):n)+'_hardsub.mp4'}}),hs=mkSrc($('hsrcS'),SUBX);
$('hname').addEventListener('input',e=>{e.target._m=!!e.target.value});
$('burn').onclick=async()=>{const v=hv.get(),s=hs.get();if(!v)return toast('Choose a video');if(!s)return toast('Choose a subtitle file');
 const name=$('hname').value.trim();$('burn').disabled=true;const x=xfer(name||v.value.split('/').pop());
 try{const r=await api('/api/hardsub',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({video:v,sub:s,name:name,font:$('hfont').value.trim(),size:$('hsize').value.trim(),crf:$('hcrf').value,preset:$('hpre').value})});const j=await r.json();
  if(!r.ok)x.end('error',j.detail||'Rejected');else poll(j.id,x)}catch(e){x.end('error','Request failed')}
 $('burn').disabled=false};
let Z=null,zmode='extract';const zsel=new Set(),zpair={};
const kindOf=p=>{const e=ext(p);return VIDX.includes(e)?'video':SUBX.includes(e)?'sub':'other'};
const bname=p=>p.split('/').pop();
const stemOf=p=>{const b=bname(p),i=b.lastIndexOf('.');return(i>0?b.slice(0,i):b).toLowerCase()};
function guessSub(v){const subs=Z.entries.filter(e=>e.kind==='sub'),s=stemOf(v);
 let m=subs.find(e=>stemOf(e.path)===s)||subs.find(e=>stemOf(e.path).startsWith(s))||subs.find(e=>s.startsWith(stemOf(e.path)));
 if(!m&&subs.length===1&&Z.entries.filter(e=>e.kind==='video').length===1)m=subs[0];return m?m.path:''}
function showStage(info){Z=info;zsel.clear();Object.keys(zpair).forEach(k=>delete zpair[k]);
 Z.entries.forEach(e=>{if(!e.enc)zsel.add(e.path);if(e.kind==='video')zpair[e.path]=guessSub(e.path)});
 zmode=Z.entries.some(e=>e.kind==='video')&&Z.entries.some(e=>e.kind==='sub')?'extract_sub':'extract';
 $('zout').value=Z.name;$('zq').value='';$('zin').hidden=true;$('zstage').hidden=false;$('zres').hidden=true;renderZ()}
function leaveStage(){Z=null;$('zstage').hidden=true;$('zin').hidden=false}
function renderZ(){if(!Z)return;const q=$('zq').value.toLowerCase(),L=Z.entries.filter(e=>e.path.toLowerCase().includes(q)),tag={video:'Video',sub:'Subtitle',other:'File'};
 $('zhead').textContent=Z.name+' · '+fmt(Z.size)+' · '+Z.entries.length+' files';
 $('zlist').innerHTML=L.length?L.map(e=>'<label class="zr"><input type="checkbox" data-p="'+esc(e.path)+'"'+(zsel.has(e.path)?' checked':'')+(e.enc?' disabled':'')+'><span class="zn">'+esc(e.path)+'</span><span class="bd '+e.kind+'">'+tag[e.kind]+(e.enc?' · locked':'')+'</span><small>'+fmt(e.size)+'</small></label>').join(''):'<div class="empty">No files match.</div>';
 renderMode()}
function renderMode(){if(!Z)return;document.querySelectorAll('#zmodes [data-m]').forEach(b=>b.setAttribute('aria-pressed',b.dataset.m===zmode));
 const sel=Z.entries.filter(e=>zsel.has(e.path)),bytes=sel.reduce((a,e)=>a+e.size,0),vids=sel.filter(e=>e.kind==='video'),others=sel.filter(e=>e.kind==='other'),subs=Z.entries.filter(e=>e.kind==='sub');
 $('zm-zip').hidden=zmode!=='zip';$('zm-extract').hidden=zmode!=='extract';$('zm-sub').hidden=zmode!=='extract_sub';
 $('zm-extract').textContent=sel.length+' file'+(sel.length===1?'':'s')+' selected ('+fmt(bytes)+'). Each will be saved to storage by its file name.';
 $('zpairs').innerHTML=vids.length?vids.map(v=>'<div class="pr"><span class="zn">'+esc(bname(v.path))+'</span><select data-v="'+esc(v.path)+'" aria-label="Subtitle for '+esc(bname(v.path))+'"><option value="">No subtitle (save as is)</option>'+subs.map(s=>'<option value="'+esc(s.path)+'"'+(zpair[v.path]===s.path?' selected':'')+'>'+esc(s.path)+'</option>').join('')+'</select></div>').join('')+(others.length?'<p class="hint">'+others.length+' other selected file'+(others.length===1?'':'s')+' will be saved unchanged.</p>':''):'<p class="hint">Select at least one video in the list above.</p>';
 $('zsave').textContent=zmode==='zip'?'Save zip to storage':zmode==='extract'?'Extract '+sel.length+' file'+(sel.length===1?'':'s')+' & save':'Add subtitles to '+vids.length+' video'+(vids.length===1?'':'s')+' & save'}
$('zlist').onchange=e=>{const p=e.target.dataset.p;if(p===undefined)return;if(e.target.checked)zsel.add(p);else zsel.delete(p);renderMode()};
$('zpairs').onchange=e=>{if(e.target.dataset.v!==undefined)zpair[e.target.dataset.v]=e.target.value};
$('zmodes').onclick=e=>{const b=e.target.closest('[data-m]');if(b){zmode=b.dataset.m;renderMode()}};
$('zq').oninput=renderZ;
$('zall').onclick=()=>{Z.entries.forEach(e=>{if(!e.enc)zsel.add(e.path)});renderZ()};
$('znone').onclick=()=>{zsel.clear();renderZ()};
$('zdiscard').onclick=async()=>{if(Z){try{await api('/api/zip/'+Z.id,{method:'DELETE'})}catch(e){}}leaveStage();toast('Discarded. Nothing was saved.')};
function zipUpload(file){const x=xfer(file.name),t0=Date.now(),r=new XMLHttpRequest();r.open('POST','/api/zip/stage?name='+encodeURIComponent(file.name));
 r.upload.onprogress=e=>{if(!e.lengthComputable)return;const p=e.loaded/e.total*100;x.set(p<100?Math.round(p)+'% · '+fmt(e.loaded/((Date.now()-t0)/1000||1))+'/s':'Reading contents…',p,p>=100)};
 r.onload=()=>{if(r.status===200){x.end('done','Ready');showStage(JSON.parse(r.responseText))}else if(r.status===401)location.href='/login';else{let m='Upload failed';try{m=JSON.parse(r.responseText).detail||m}catch(e){}x.end('error',m)}};
 r.onerror=()=>x.end('error','Network error');r.send(file)}
const zd=$('zdrop');['dragover','dragenter'].forEach(e=>zd.addEventListener(e,ev=>{ev.preventDefault();zd.classList.add('over')}));
['dragleave','drop'].forEach(e=>zd.addEventListener(e,ev=>{ev.preventDefault();zd.classList.remove('over')}));
zd.addEventListener('drop',e=>{const f=e.dataTransfer.files[0];if(f)zipUpload(f)});$('zpick').onchange=e=>{if(e.target.files[0])zipUpload(e.target.files[0]);e.target.value=''};
const zs=mkSrc($('zsrc'),['zip'],null);
$('zload').onclick=async()=>{const src=zs.get();if(!src)return toast('Choose a zip or paste a link');const x=xfer(src.value.split('/').pop()||'zip');
 try{const r=await api('/api/zip/stage-url',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({source:src})});const j=await r.json();
  if(!r.ok)x.end('error',j.detail||'Rejected');else poll(j.id,x,j=>showStage(j.result))}catch(e){x.end('error','Request failed')}};
function showResult(files){const r=$('zres');r.hidden=false;
 r.innerHTML='<p class="hint" style="padding:10px 14px;margin:0"><b>Saved '+files.length+' file'+(files.length===1?'':'s')+' to storage.</b></p>'+files.map(f=>'<div class="f"><span class="n">'+esc(f.name)+'</span><span class="sz">'+fmt(f.size)+'</span><span class="a"><button class="btn ghost sm" data-c="'+esc(f.cdn_url)+'">Copy stream link</button><button class="btn ghost sm" data-c="'+esc(f.download_url)+'">Copy download link</button></span></div>').join('')}
$('zres').onclick=e=>{const b=e.target.closest('button[data-c]');if(b)copy(b.dataset.c)};
$('zsave').onclick=async()=>{if(!Z)return;const sel=Z.entries.filter(e=>zsel.has(e.path));const body={id:Z.id,mode:zmode};
 if(zmode==='zip')body.name=$('zout').value.trim()||Z.name;
 else if(zmode==='extract'){if(!sel.length)return toast('Select at least one file');body.files=sel.map(e=>e.path)}
 else{const vids=sel.filter(e=>e.kind==='video');if(!vids.length)return toast('Select at least one video');
  body.pairs=vids.map(e=>({video:e.path,sub:zpair[e.path]||null}));body.files=sel.filter(e=>e.kind==='other').map(e=>e.path);body.lang=$('zlang').value.trim()||'si';body.track=$('ztrack').value.trim()}
 $('zsave').disabled=true;const x=xfer(Z.name);
 try{const r=await api('/api/zip/commit',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)});const j=await r.json();
  if(!r.ok)x.end('error',j.detail||'Rejected');else{leaveStage();poll(j.id,x,j=>{showResult(j.result.files);load()})}}catch(e){x.end('error','Request failed')}
 $('zsave').disabled=false};
(async()=>{try{const m=await(await fetch('/api/me')).json();if(m.auth_enabled&&!m.authenticated)return location.href='/login?next=%2F';$('who').textContent=m.auth_enabled?m.username:'';if(!m.auth_enabled)$('lo').remove()}catch(e){}load()})();
</script></body></html>"""

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
    return {"status": "ok", "time": time.time(), "hf_configured": bool(hf_api), "repo": HF_REPO or None,
            "auth_enabled": AUTH_ENABLED, "telegram_ok": tg_state["ok"],
            "mkvmerge": bool(shutil.which("mkvmerge")), "ffmpeg": bool(shutil.which("ffmpeg")), "fast_upload": os.environ.get("HF_HUB_ENABLE_HF_TRANSFER") == "1",
            **({"telegram_error": tg_state["error"]} if DEBUG_ERRORS else {})}

@app.get("/api/me")
def api_me(request: Request):
    user = get_current_user(request)
    return {"auth_enabled": AUTH_ENABLED, "authenticated": bool(user) or not AUTH_ENABLED,
            "username": user or "anonymous"}

@app.get("/api/files")
async def api_files(request: Request):
    require_login(request)
    if not hf_api:
        return {"items": [], "error": "HF_TOKEN is not configured"}
    try:
        items = [{**f, **links(f["name"], request)} for f in await list_files()]
        return {"items": items, "count": len(items)}
    except Exception as e:
        log.error("List failed: %s", e)
        return {"items": [], "error": str(e)}

@app.delete("/api/files/{name:path}")
async def api_delete(request: Request, name: str):
    require_login(request)
    name = safe_name(name)
    try:
        await asyncio.to_thread(hf_api.delete_file, path_in_repo=name, repo_id=HF_REPO,
                                repo_type="dataset", commit_message=f"Delete: {name}")
    except Exception as e:
        raise HTTPException(500, str(e))
    _cache["t"] = 0
    return {"success": True}

@app.post("/api/upload")
async def api_upload(request: Request, name: str = ""):
    """Raw-body upload: the browser sends the file bytes directly, we stream them to disk (no multipart re-copy)."""
    require_login(request)
    if not hf_api:
        raise HTTPException(500, "HF_TOKEN is not configured")
    try:
        fname = safe_name(name)
    except HTTPException:
        fname = f"file_{uuid.uuid4().hex[:8]}"
    declared = int(request.headers.get("content-length") or 0)
    if declared > MAX_FILE_SIZE:
        raise HTTPException(413, "File is larger than the size limit")
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
        t0 = time.time()
        await push_to_hf(tmp, fname, "Web upload")
        log.info("Web upload %s: %.1f MB, storage push %.1fs", fname, size / 1048576, time.time() - t0)
        return {"success": True, "filename": fname, "size": size, **links(fname, request)}
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
    if not hf_api:
        raise HTTPException(500, "HF_TOKEN is not configured")
    body = await request.json()
    url, name = str(body.get("url", "")).strip(), str(body.get("name", "")).strip()
    try:
        await assert_public(url)
        if name:
            safe_name(name)
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(400, str(e) or "Invalid link")
    job = new_job(name or url)
    asyncio.create_task(run_remote(job, url, name))
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
    if not hf_api:
        raise HTTPException(500, "HF_TOKEN is not configured")
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
    if not hf_api:
        raise HTTPException(500, "HF_TOKEN is not configured")
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

@app.post("/api/zip/stage")
async def api_zip_stage(request: Request, name: str = ""):
    """Receive a zip and list its contents. Nothing is saved to storage yet."""
    require_login(request)
    try:
        fname = safe_name(name)
    except HTTPException:
        fname = "archive.zip"
    declared = int(request.headers.get("content-length") or 0)
    if declared > MAX_FILE_SIZE:
        raise HTTPException(413, "File is larger than the size limit")
    sid = uuid.uuid4().hex[:12]
    d = STAGE_ROOT / sid
    d.mkdir(parents=True, exist_ok=True)
    path, size = d / "archive.zip", 0
    try:
        async with aiofiles.open(path, "wb") as out:
            async for chunk in request.stream():
                size += len(chunk)
                if size > MAX_FILE_SIZE:
                    raise HTTPException(413, "File is larger than the size limit")
                await out.write(chunk)
        if size == 0:
            raise HTTPException(400, "Empty upload")
        return await finish_stage(sid, d, path, fname)
    except HTTPException:
        shutil.rmtree(d, ignore_errors=True)
        raise
    except Exception as e:
        shutil.rmtree(d, ignore_errors=True)
        raise HTTPException(400, str(e) or "Could not read the zip")

@app.post("/api/zip/stage-url")
async def api_zip_stage_url(request: Request):
    require_login(request)
    b = await request.json()
    src = b.get("source") or {}
    kind, val = src.get("type"), str(src.get("value", "")).strip()
    if kind not in ("storage", "url") or not val:
        raise HTTPException(400, "Choose a zip from storage or paste a link")
    if kind == "url":
        try:
            await assert_public(val)
        except Exception as e:
            raise HTTPException(400, str(e) or "Invalid link")
    else:
        safe_name(val)
    job = new_job(val)
    asyncio.create_task(run_stage_url(job, {"type": kind, "value": val}))
    return {"id": job["id"]}

@app.delete("/api/zip/{sid}")
async def api_zip_discard(request: Request, sid: str):
    require_login(request)
    if STAGES.get(sid, {}).get("busy"):
        raise HTTPException(409, "This zip is being saved right now")
    drop_stage(sid)
    return {"success": True}

@app.post("/api/zip/commit")
async def api_zip_commit(request: Request):
    require_login(request)
    if not hf_api:
        raise HTTPException(500, "HF_TOKEN is not configured")
    b = await request.json()
    sid = str(b.get("id", ""))
    st = STAGES.get(sid)
    if not st:
        raise HTTPException(404, "This zip expired. Please upload it again.")
    if st["busy"]:
        raise HTTPException(409, "This zip is already being saved")
    mode = b.get("mode")
    if mode not in ("zip", "extract", "extract_sub"):
        raise HTTPException(400, "Unknown action")
    known = {e["path"]: e for e in st["entries"]}
    files = [x for x in (b.get("files") or []) if isinstance(x, str) and x in known] if mode != "zip" else []
    pairs = []
    if mode == "extract_sub":
        for pr in b.get("pairs") or []:
            v, sub = pr.get("video"), pr.get("sub") or None
            if v in known and (sub is None or sub in known):
                pairs.append({"video": v, "sub": sub})
    if mode == "extract" and not files:
        raise HTTPException(400, "Select at least one file")
    if mode == "extract_sub" and not (pairs or files):
        raise HTTPException(400, "Select at least one video")
    if any(known[x]["enc"] for x in files + [q["video"] for q in pairs] + [q["sub"] for q in pairs if q["sub"]]):
        raise HTTPException(400, "Password-protected files can't be extracted")
    lang = str(b.get("lang") or "si").strip()
    if not re.fullmatch(r"[A-Za-z]{2,3}(-[A-Za-z0-9]{2,8})?", lang):
        raise HTTPException(400, "Language must be an ISO code such as si or en")
    track = " ".join(str(b.get("track") or "").split())[:120]
    job = new_job(st["name"])
    asyncio.create_task(run_zip_commit(job, sid, st, mode, files, pairs, lang, track, str(b.get("name") or "")))
    return {"id": job["id"]}

@app.get("/api/jobs/{job_id}")
def api_job(request: Request, job_id: str):
    require_login(request)
    job = JOBS.get(job_id)
    if not job:
        raise HTTPException(404, "Unknown job")
    return job

@app.get("/cdn/{filename:path}")
def cdn(request: Request, filename: str):
    return download_guard(request) or RedirectResponse(hf_url(filename), 302)

@app.get("/download/{filename:path}")
def download(request: Request, filename: str):
    return download_guard(request) or RedirectResponse(hf_url(filename, True), 302)

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
        if not hf_api:
            return await event.reply("Storage is not configured.")
        try:
            names = [f["name"] for f in await list_files()]
            await event.reply("No files yet." if not names else f"Files ({len(names)}):\n" + "\n".join("• " + n for n in names[:50]))
        except Exception as e:
            await event.reply(f"Error: {e}")

    @client.on(events.NewMessage())
    async def _file(event):
        m = event.message
        if not hf_api or not m.file or (m.text or "").startswith("/"):
            return
        status = await event.reply("Preparing…")
        fname = Path(getattr(m.file, "name", None) or "").name
        if not fname:
            ext = ".jpg" if m.photo else (getattr(m.file, "ext", None) or ".bin")
            fname = f"tg_{m.id}{ext if ext.startswith('.') else '.' + ext}"
        total = int(getattr(m.file, "size", 0) or 0)
        tmp = pick_tmp(total) / f"{uuid.uuid4().hex}_{fname}"
        last = {"t": 0.0}
        t0 = time.time()

        async def edit(text):
            try:
                await status.edit(text)
            except Exception:
                pass

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
                        await edit(f"Streaming {fname} to storage\n{pct}% (no disk used)")
                except asyncio.CancelledError:
                    pass

            rep = asyncio.create_task(report())
            try:
                await asyncio.to_thread(hf_api.upload_file, path_or_fileobj=stream, path_in_repo=fname,
                                        repo_id=HF_REPO, repo_type="dataset",
                                        commit_message=f"Telegram stream upload: {fname}")
                _cache["t"] = 0
                l = links(fname)
                await edit(f"Done: {fname} ({total / 1048576:.1f} MB)\n\nDownload:\n{l['download_url']}\n\nStream:\n{l['cdn_url']}")
                log.info("TG STREAM upload OK %s: %.1f MB in %.1fs, served %.1f MB",
                         fname, total / 1048576, time.time() - t0, stream.bytes_served / 1048576)
                return
            except Exception as e:
                log.warning("Stream upload failed (%s: %s) -> falling back to temp-file mode", type(e).__name__, e)
            finally:
                rep.cancel()

        try:
            await client.download_media(m, file=str(tmp), progress_callback=progress)
            size = tmp.stat().st_size
            t1 = time.time()
            await edit(f"Saving {size / 1048576:.0f} MB to storage…")
            await push_to_hf(tmp, fname, "Telegram upload")
            l = links(fname)
            await edit(f"Done: {fname} ({size / 1048576:.1f} MB)\n\nDownload:\n{l['download_url']}\n\nStream:\n{l['cdn_url']}")
            log.info("TG upload %s: dl %.1fs, push %.1fs", fname, t1 - t0, time.time() - t1)
        except Exception as e:
            log.error("TG upload failed: %s", e)
            await edit(f"Failed: {type(e).__name__}: {str(e)[:200]}")
        finally:
            tmp.unlink(missing_ok=True)

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=int(os.getenv("PORT", "7860")))
