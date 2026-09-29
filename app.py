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
from huggingface_hub import HfApi
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
.panel{background:var(--card);border:1px solid var(--line);border-radius:14px;overflow:hidden}
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
</style></head><body>
<header><div class="logo">My Cloud</div><div><span id="who" style="color:var(--mute);margin-right:10px"></span><form id="lo" method="post" action="/logout" style="display:inline"><button class="btn ghost sm">Sign out</button></form></div></header>
<main>
<h1>Put a file online.</h1>
<p class="lead">Upload from this device or paste a link. You get a download link and a streaming link that plays in a browser or video player.</p>
<div class="panel">
 <div class="tabs" role="tablist">
  <button class="tab" role="tab" id="t1" aria-selected="true" aria-controls="p1">From this device</button>
  <button class="tab" role="tab" id="t2" aria-selected="false" aria-controls="p2">From a link</button>
 </div>
 <div class="pane" id="p1" role="tabpanel">
  <label class="drop" id="drop" for="pick"><b>Drop files here or choose them</b><span>Up to 20&nbsp;GB each. Videos work best as MP4.</span></label>
  <input type="file" id="pick" multiple hidden>
 </div>
 <div class="pane" id="p2" role="tabpanel" hidden>
  <textarea id="urls" placeholder="https://example.com/video.mp4&#10;One link per line" aria-label="File links"></textarea>
  <div class="row"><input type="text" id="rname" placeholder="Save as (optional, single link only)" aria-label="File name"><button class="btn" id="fetch">Fetch to cloud</button></div>
  <p class="hint">The server downloads the file directly, so nothing passes through your device.</p>
 </div>
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
function upload(file){const x=xfer(file.name),t0=Date.now();const r=new XMLHttpRequest();
 r.open('POST','/api/upload?name='+encodeURIComponent(file.name));
 r.upload.onprogress=e=>{if(!e.lengthComputable)return;const p=e.loaded/e.total*100,s=e.loaded/((Date.now()-t0)/1000||1);x.set(p<100?Math.round(p)+'% · '+fmt(s)+'/s':'Saving to storage…',p,p>=100)};
 r.onload=()=>{if(r.status===200){x.end('done','Done');toast('Uploaded '+file.name);load()}else if(r.status===401)location.href='/login';else{let m='Upload failed';try{m=JSON.parse(r.responseText).detail||m}catch(e){}x.end('error',m)}};
 r.onerror=()=>x.end('error','Network error');r.send(file)}
const drop=$('drop');['dragover','dragenter'].forEach(e=>drop.addEventListener(e,ev=>{ev.preventDefault();drop.classList.add('over')}));
['dragleave','drop'].forEach(e=>drop.addEventListener(e,ev=>{ev.preventDefault();drop.classList.remove('over')}));
drop.addEventListener('drop',e=>[...e.dataTransfer.files].forEach(upload));$('pick').onchange=e=>{[...e.target.files].forEach(upload);e.target.value=''};
$('fetch').onclick=async()=>{const urls=$('urls').value.split(/\\s+/).filter(Boolean);if(!urls.length)return toast('Paste at least one link');
 const name=urls.length===1?$('rname').value.trim():'';$('fetch').disabled=true;
 for(const url of urls){const x=xfer(url.split('/').pop()||url);
  try{const r=await api('/api/remote',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({url,name})});const j=await r.json();
   if(!r.ok){x.end('error',j.detail||'Rejected');continue}poll(j.id,x)}catch(e){x.end('error','Request failed')}}
 $('urls').value='';$('rname').value='';$('fetch').disabled=false};
async function poll(id,x){const r=await api('/api/jobs/'+id);const j=await r.json();
 if(j.stage==='downloading')x.set('Downloading '+(j.total?Math.round(j.done/j.total*100)+'% · ':'')+fmt(j.speed)+'/s',j.total?j.done/j.total*100:null,!j.total);
 else if(j.stage==='uploading')x.set('Saving to storage…',100,true);
 else if(j.stage==='done'){x.end('done','Done');toast('Saved '+j.name);load();return}
 else if(j.stage==='error'){x.end('error',j.error||'Failed');return}
 setTimeout(()=>poll(id,x),700)}
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
            "fast_upload": os.environ.get("HF_HUB_ENABLE_HF_TRANSFER") == "1",
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
