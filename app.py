import os
import sys
import json
import time
import hmac
import html as html_lib
import hashlib
import secrets
import base64
import asyncio
import logging
import aiofiles
import uuid
import traceback
from pathlib import Path, PurePosixPath
from urllib.parse import quote
from datetime import datetime

from fastapi import (
    FastAPI,
    Request,
    Form,
    File,
    UploadFile,
    HTTPException,
)
from fastapi.responses import HTMLResponse, RedirectResponse, JSONResponse
from starlette.middleware.base import BaseHTTPMiddleware

from huggingface_hub import HfApi
from telethon import TelegramClient, events
from telethon.sessions import MemorySession


# ══════════════════════════════════════════════════════════════
# Logging
# ══════════════════════════════════════════════════════════════
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)],
)
logger = logging.getLogger("MyCloud")


# ══════════════════════════════════════════════════════════════
# Helpers
# ══════════════════════════════════════════════════════════════
def env_bool(name: str, default: bool = False) -> bool:
    val = os.getenv(name, str(default)).strip().lower()
    return val in {"1", "true", "yes", "on"}


def b64encode(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).decode().rstrip("=")


def b64decode(data: str) -> bytes:
    padding = "=" * (-len(data) % 4)
    return base64.urlsafe_b64decode((data + padding).encode())


SCRYPT_MAXMEM = 64 * 1024 * 1024  # 64 MiB, explicit (avoids OpenSSL default quirks)


def hash_password(password: str) -> str:
    """
    scrypt password hash.
    Format: scrypt$N$r$p$salt_b64$hash_b64
    """
    salt = os.urandom(16)
    dk = hashlib.scrypt(
        password.encode("utf-8"),
        salt=salt,
        n=16384,
        r=8,
        p=1,
        dklen=32,
        maxmem=SCRYPT_MAXMEM,
    )
    return f"scrypt$16384$8$1${b64encode(salt)}${b64encode(dk)}"


def verify_password(password: str, encoded_hash: str) -> bool:
    """
    Verify a password against a stored scrypt hash. NEVER raises.
    Accepts both our format (scrypt$N$r$p$salt$hash) and passlib-style
    (scrypt:N:r:p$salt$hash). Falls back to a constant-time plaintext
    compare against ADMIN_PASSWORD if the hash cannot be used.
    """
    try:
        if not password or not encoded_hash:
            return False

        normalized = encoded_hash.strip()

        # passlib format: scrypt:16384:8:1$salt$hash  ->  scrypt$16384$8$1$salt$hash
        if normalized.startswith("scrypt:"):
            normalized = "scrypt$" + normalized[len("scrypt:"):].replace(":", "$", 3)

        parts = normalized.split("$")
        if len(parts) != 6 or parts[0] != "scrypt":
            raise ValueError("unsupported hash format")

        _, n, r, p, salt_b64, hash_b64 = parts
        salt = b64decode(salt_b64)
        expected = b64decode(hash_b64)

        dk = hashlib.scrypt(
            password.encode("utf-8"),
            salt=salt,
            n=int(n),
            r=int(r),
            p=int(p),
            dklen=len(expected),
            maxmem=SCRYPT_MAXMEM,
        )

        return hmac.compare_digest(dk, expected)

    except Exception:
        # Last-resort fallback: constant-time compare against plaintext env var.
        # Only possible when ADMIN_PASSWORD is set (never log it!).
        if ADMIN_PASSWORD:
            try:
                return hmac.compare_digest(
                    (password or "").encode("utf-8"),
                    ADMIN_PASSWORD.encode("utf-8"),
                )
            except Exception:
                return False
        return False


# ══════════════════════════════════════════════════════════════
# Secrets / Config
# ══════════════════════════════════════════════════════════════
HF_TOKEN = os.environ.get("HF_TOKEN", "").strip()
HF_REPO = os.environ.get("HF_REPO", "").strip()

API_ID = int(os.environ.get("TG_API_ID", "0") or "0")
API_HASH = os.environ.get("TG_API_HASH", "").strip()
BOT_TOKEN = os.environ.get("TG_BOT_TOKEN", "").strip()

PUBLIC_BASE_URL = os.getenv("PUBLIC_BASE_URL", "").strip().rstrip("/")

ADMIN_USERNAME = os.getenv("ADMIN_USERNAME", "").strip()
ADMIN_PASSWORD = os.getenv("ADMIN_PASSWORD", "").strip()
ADMIN_PASSWORD_HASH = os.getenv("ADMIN_PASSWORD_HASH", "").strip()

SESSION_SECRET_RAW = os.getenv("SESSION_SECRET", "").strip()
SESSION_MAX_AGE = int(os.getenv("SESSION_MAX_AGE", "86400"))  # 24 hours
COOKIE_NAME = os.getenv("COOKIE_NAME", "mc_session")

PROTECT_DOWNLOADS = env_bool("PROTECT_DOWNLOADS", False)
DEBUG_ERRORS = env_bool("DEBUG_ERRORS", False)

MAX_FILE_SIZE = int(os.getenv("MAX_FILE_SIZE", str(2 * 1024 * 1024 * 1024)))  # 2 GB
def _pick_tmp_dir() -> str:
    """Prefer tmpfs (RAM disk, e.g. /dev/shm) so temp files never hit the disk."""
    for candidate in (os.getenv("TMP_DIR", ""), "/dev/shm/mycloud", "/tmp/mycloud"):
        if not candidate:
            continue
        try:
            p = Path(candidate)
            p.mkdir(parents=True, exist_ok=True)
            probe = p / ".write_probe"
            probe.write_bytes(b"x")
            probe.unlink()
            return candidate
        except Exception:
            continue
    return "/tmp/mycloud"


TMP_DIR = Path(_pick_tmp_dir())
logger.info(f"Temp dir: {TMP_DIR}")
TMP_DIR.mkdir(parents=True, exist_ok=True)

# Login brute-force protection
MAX_FAILED_ATTEMPTS = int(os.getenv("MAX_FAILED_ATTEMPTS", "5"))
LOCK_SECONDS = int(os.getenv("LOCK_SECONDS", "300"))
failed_attempts = {}

# Telegram and startup status
TELEGRAM_OK = False
TELEGRAM_ERROR = None
STARTUP_ERROR = None


# ══════════════════════════════════════════════════════════════
# Session secret
# ══════════════════════════════════════════════════════════════
if SESSION_SECRET_RAW:
    SESSION_SECRET = SESSION_SECRET_RAW.encode("utf-8")
else:
    SESSION_SECRET = hashlib.sha256(
        f"{HF_TOKEN}|{BOT_TOKEN}|{HF_REPO}|{ADMIN_USERNAME}".encode("utf-8")
    ).digest()
    logger.warning(
        "SESSION_SECRET is not set. Derived temporary secret from other secrets. "
        "Set SESSION_SECRET for stable sessions across restarts."
    )


# ══════════════════════════════════════════════════════════════
# Auth config
# ══════════════════════════════════════════════════════════════
if ADMIN_PASSWORD_HASH:
    PASSWORD_HASH = ADMIN_PASSWORD_HASH
elif ADMIN_PASSWORD:
    PASSWORD_HASH = hash_password(ADMIN_PASSWORD)
    logger.warning(
        "ADMIN_PASSWORD is set as plaintext. Prefer ADMIN_PASSWORD_HASH in production."
    )
else:
    PASSWORD_HASH = ""

AUTH_ENABLED = bool(ADMIN_USERNAME and PASSWORD_HASH)

if not AUTH_ENABLED:
    logger.warning(
        "ADMIN_USERNAME / ADMIN_PASSWORD or ADMIN_PASSWORD_HASH not set. "
        "Web auth is disabled."
    )

if PROTECT_DOWNLOADS and not AUTH_ENABLED:
    logger.warning(
        "PROTECT_DOWNLOADS=true but auth is disabled. "
        "Download protection will not work properly."
    )


# ══════════════════════════════════════════════════════════════
# Clients
# ══════════════════════════════════════════════════════════════
hf_api = HfApi(token=HF_TOKEN) if HF_TOKEN else None
app = FastAPI(title="My Cloud")
client = TelegramClient(MemorySession(), API_ID, API_HASH) if API_ID and API_HASH else None


# ══════════════════════════════════════════════════════════════
# Session token
# ══════════════════════════════════════════════════════════════
def create_session_token(username: str) -> str:
    now = int(time.time())
    payload = {
        "sub": username,
        "iat": now,
        "exp": now + SESSION_MAX_AGE,
        "jti": secrets.token_hex(16),
    }

    body = b64encode(json.dumps(payload, separators=(",", ":")).encode("utf-8"))
    signature = b64encode(
        hmac.new(SESSION_SECRET, body.encode("utf-8"), hashlib.sha256).digest()
    )

    return f"{body}.{signature}"


def parse_session_token(token: str | None) -> dict | None:
    """
    Parse and validate session token. Never throws.
    Returns None on any invalid token.
    """
    try:
        if not token or not isinstance(token, str):
            return None

        if token.count(".") != 1:
            return None

        body, signature = token.split(".", 1)

        if not body or not signature:
            return None

        try:
            payload = json.loads(b64decode(body))
        except Exception:
            return None

        if not isinstance(payload, dict):
            return None

        expected_signature = b64encode(
            hmac.new(SESSION_SECRET, body.encode("utf-8"), hashlib.sha256).digest()
        )

        if not hmac.compare_digest(signature, expected_signature):
            return None

        try:
            exp = int(payload.get("exp", 0))
        except (TypeError, ValueError):
            return None

        if exp < int(time.time()):
            return None

        username = payload.get("sub")
        if not username or not isinstance(username, str) or not username.strip():
            return None

        return payload

    except Exception:
        return None


def get_current_user(request: Request) -> str | None:
    """
    Get authenticated username from session cookie.
    Never throws.
    """
    try:
        token = request.cookies.get(COOKIE_NAME)
        payload = parse_session_token(token)
        if not payload:
            return None
        return payload.get("sub")
    except Exception:
        return None


def is_https_request(request: Request) -> bool:
    try:
        forwarded = request.headers.get("x-forwarded-proto", "")
        if forwarded:
            return forwarded.split(",")[0].strip() == "https"

        if PUBLIC_BASE_URL.startswith("https://"):
            return True

        return request.url.scheme == "https"
    except Exception:
        return False


def safe_next_url(next_url: str | None) -> str:
    if not next_url:
        return "/"

    next_url = next_url.strip()

    if not next_url.startswith("/"):
        return "/"

    if next_url.startswith("//"):
        return "/"

    return next_url


def purge_failed_attempts() -> None:
    now = time.time()
    if len(failed_attempts) > 10000:
        for ip, (_, locked_until) in list(failed_attempts.items()):
            if locked_until and locked_until < now:
                failed_attempts.pop(ip, None)


# ══════════════════════════════════════════════════════════════
# Path / URL helpers
# ══════════════════════════════════════════════════════════════
def safe_relative_path(filename: str) -> str:
    filename = (filename or "").strip()

    if not filename:
        raise HTTPException(status_code=400, detail="Invalid filename")

    path = PurePosixPath(filename)

    if (
        path.is_absolute()
        or ".." in path.parts
        or path.as_posix() in {"", "."}
    ):
        raise HTTPException(status_code=400, detail="Invalid file path")

    return path.as_posix()


def encode_path(path: str) -> str:
    return quote(path, safe="/")


def direct_hf_url(filename: str, download: bool = False) -> str:
    safe = safe_relative_path(filename)
    encoded = encode_path(safe)

    url = f"https://huggingface.co/datasets/{HF_REPO}/resolve/main/{encoded}"

    if download:
        url += "?download=true"

    return url


def get_base_url(request: Request | None = None) -> str:
    if PUBLIC_BASE_URL:
        return PUBLIC_BASE_URL

    if request is None:
        return ""

    try:
        raw_proto = request.headers.get("x-forwarded-proto") or request.url.scheme
        raw_host = (
            request.headers.get("x-forwarded-host")
            or request.headers.get("host")
            or request.url.netloc
        )

        proto = raw_proto.split(",")[0].strip() if raw_proto else ""
        host = raw_host.split(",")[0].strip() if raw_host else ""

        if not proto or not host:
            return ""

        return f"{proto}://{host}".rstrip("/")
    except Exception:
        return ""


def build_download_url(filename: str, request: Request | None = None) -> str:
    safe = safe_relative_path(filename)
    encoded = encode_path(safe)

    base = get_base_url(request)

    if base:
        return f"{base}/download/{encoded}"

    return direct_hf_url(filename, download=True)


def build_cdn_url(filename: str, request: Request | None = None) -> str:
    safe = safe_relative_path(filename)
    encoded = encode_path(safe)

    base = get_base_url(request)

    if base:
        return f"{base}/cdn/{encoded}"

    return direct_hf_url(filename, download=False)


# ══════════════════════════════════════════════════════════════
# Global Exception Middleware
# ══════════════════════════════════════════════════════════════
ERROR_HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Error</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{
  font-family:'Segoe UI',system-ui,-apple-system,sans-serif;
  background:#0a0a0f;
  color:#e0e0e0;
  padding:20px;
  min-height:100vh;
  display:flex;
  align-items:center;
  justify-content:center;
}
.error-box{
  max-width:600px;
  background:#1a1a24;
  border:1px solid #2a2a3a;
  border-radius:16px;
  padding:30px;
}
h1{color:#ef4444;margin-bottom:12px}
.error-id{color:#888;font-size:.9rem;margin-bottom:20px}
p{color:#c4b5fd;font-size:.95rem;line-height:1.6;margin-bottom:12px}
.details{
  background:#0a0a0f;
  border:1px solid #1d1d2b;
  border-radius:8px;
  padding:12px;
  font-family:monospace;
  font-size:.8rem;
  color:#888;
  overflow-x:auto;
  margin-top:16px;
  white-space:pre-wrap;
  word-break:break-all;
}
a{color:#818cf8;text-decoration:none}
a:hover{text-decoration:underline}
</style>
</head>
<body>
  <div class="error-box">
    <h1>❌ Internal Server Error</h1>
    <div class="error-id">Error ID: %%ERROR_ID%%</div>
    <p>Something went wrong. Please try again later or contact support.</p>
    <p><a href="/">← Back to Home</a></p>
    %%DETAILS%%
  </div>
</body>
</html>"""


class GlobalExceptionMiddleware(BaseHTTPMiddleware):
    async def dispatch(self, request: Request, call_next):
        try:
            response = await call_next(request)
            return response
        except Exception as exc:
            error_id = secrets.token_hex(8)
            tb_str = traceback.format_exc()
            logger.error(f"Unhandled exception [{error_id}]:\n{tb_str}")

            # Determine if client expects JSON
            accept_header = request.headers.get("accept", "").lower()
            is_json_request = (
                "application/json" in accept_header
                or request.url.path.startswith("/api/")
            )

            if is_json_request:
                data = {
                    "error": "Internal Server Error",
                    "error_id": error_id,
                    "status": 500,
                }
                if DEBUG_ERRORS:
                    data["exception"] = type(exc).__name__
                    data["message"] = str(exc)
                    data["traceback"] = tb_str

                return JSONResponse(data, status_code=500)

            else:
                details = ""
                if DEBUG_ERRORS:
                    summary = html_lib.escape(f"{type(exc).__name__}: {exc}")
                    details = f"""
    <p style="color:#f87171"><b>{summary}</b></p>
    <div class="details">{html_lib.escape(tb_str)}</div>"""

                html = (
                    ERROR_HTML_TEMPLATE
                    .replace("%%ERROR_ID%%", html_lib.escape(error_id))
                    .replace("%%DETAILS%%", details)
                )

                return HTMLResponse(html, status_code=500)


app.add_middleware(GlobalExceptionMiddleware)


# ══════════════════════════════════════════════════════════════
# Embedded Web UI
# No secrets are hardcoded in frontend.
# ══════════════════════════════════════════════════════════════
LOGIN_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Login - My Cloud</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{
  font-family:'Segoe UI',system-ui,-apple-system,sans-serif;
  background:radial-gradient(circle at top,#1a1a2e 0%,#0a0a0f 55%,#050508 100%);
  color:#e0e0e0;
  min-height:100vh;
  display:flex;
  align-items:center;
  justify-content:center;
  padding:20px;
}
.login-card{
  width:100%;
  max-width:420px;
  background:rgba(18,18,26,0.92);
  border:1px solid rgba(99,102,241,0.22);
  border-radius:20px;
  padding:32px;
  box-shadow:0 20px 60px rgba(0,0,0,0.45);
  backdrop-filter:blur(12px);
}
.brand{
  text-align:center;
  margin-bottom:28px;
}
.brand h1{
  font-size:1.8rem;
  background:linear-gradient(135deg,#6366f1,#a855f7,#ec4899);
  -webkit-background-clip:text;
  -webkit-text-fill-color:transparent;
}
.brand p{
  color:#888;
  font-size:.92rem;
  margin-top:8px;
}
.field{
  margin-bottom:18px;
}
.field label{
  display:block;
  font-size:.85rem;
  color:#aaa;
  margin-bottom:8px;
}
.field input{
  width:100%;
  background:#0a0a0f;
  border:1px solid #2a2a3a;
  border-radius:12px;
  padding:13px 14px;
  color:#fff;
  outline:none;
  font-size:.95rem;
  transition:border-color .2s, box-shadow .2s;
}
.field input:focus{
  border-color:#6366f1;
  box-shadow:0 0 0 3px rgba(99,102,241,0.15);
}
.btn{
  width:100%;
  background:linear-gradient(135deg,#6366f1,#8b5cf6);
  color:#fff;
  border:none;
  border-radius:12px;
  padding:13px 16px;
  font-size:.98rem;
  font-weight:600;
  cursor:pointer;
  transition:transform .15s ease, opacity .2s ease;
}
.btn:hover{
  transform:translateY(-1px);
  opacity:.95;
}
.error{
  background:rgba(239,68,68,0.12);
  border:1px solid rgba(239,68,68,0.35);
  color:#fca5a5;
  padding:12px 14px;
  border-radius:12px;
  font-size:.9rem;
  margin-bottom:18px;
}
.footer-note{
  text-align:center;
  margin-top:22px;
  color:#555;
  font-size:.78rem;
}
</style>
</head>
<body>
  <div class="login-card">
    <div class="brand">
      <h1>☁️ My Cloud</h1>
      <p>Sign in to manage uploads and links</p>
    </div>

    %%ERROR%%

    <form method="post" action="/login">
      <input type="hidden" name="next" value="%%NEXT%%">

      <div class="field">
        <label for="username">Username</label>
        <input id="username" name="username" type="text" autocomplete="username" required>
      </div>

      <div class="field">
        <label for="password">Password</label>
        <input id="password" name="password" type="password" autocomplete="current-password" required>
      </div>

      <button class="btn" type="submit">Login</button>
    </form>

    <div class="footer-note">
      Secure session • HttpOnly cookie • Server-side auth
    </div>
  </div>
</body>
</html>"""


DASHBOARD_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>My Cloud</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{
  font-family:'Segoe UI',system-ui,-apple-system,sans-serif;
  background:#0a0a0f;
  color:#e0e0e0;
  min-height:100vh;
}
.topbar{
  display:flex;
  justify-content:space-between;
  align-items:center;
  gap:12px;
  padding:18px 22px;
  border-bottom:1px solid #171722;
  background:rgba(10,10,15,0.85);
  position:sticky;
  top:0;
  z-index:20;
  backdrop-filter:blur(10px);
}
.brand{
  font-weight:700;
  font-size:1.1rem;
  background:linear-gradient(135deg,#6366f1,#a855f7,#ec4899);
  -webkit-background-clip:text;
  -webkit-text-fill-color:transparent;
}
.badge{
  display:inline-block;
  padding:6px 10px;
  border-radius:999px;
  font-size:.75rem;
  border:1px solid #2a2a3a;
  color:#9ca3af;
  background:#111118;
}
.user-box{
  display:flex;
  align-items:center;
  gap:10px;
  font-size:.9rem;
  color:#d1d5db;
}
.btn{
  background:#6366f1;
  color:#fff;
  border:none;
  border-radius:10px;
  padding:9px 14px;
  cursor:pointer;
  font-size:.85rem;
  transition:background .2s;
}
.btn:hover{background:#4f46e5}
.btn.small{padding:8px 12px;font-size:.8rem}
.btn.ghost{
  background:transparent;
  border:1px solid #2a2a3a;
  color:#cbd5e1;
}
.btn.ghost:hover{background:#15151f}
.container{
  max-width:860px;
  margin:0 auto;
  padding:28px 20px 60px;
}
.hero{
  text-align:center;
  margin-bottom:26px;
}
.hero h1{
  font-size:1.9rem;
  margin-bottom:8px;
}
.hero p{
  color:#888;
  font-size:.95rem;
}
.drop-zone{
  border:2px dashed #2a2a3a;
  border-radius:18px;
  padding:58px 20px;
  text-align:center;
  cursor:pointer;
  transition:all .25s;
  background:#101018;
}
.drop-zone:hover,
.drop-zone.dragover{
  border-color:#6366f1;
  background:#141423;
}
.drop-zone .icon{
  font-size:2.8rem;
  margin-bottom:12px;
}
.drop-zone p{
  color:#8b8b9a;
  font-size:.95rem;
}
.drop-zone .browse{
  color:#818cf8;
  text-decoration:underline;
  cursor:pointer;
}
#fileInput{display:none}
.progress-wrap{
  display:none;
  margin-top:22px;
  background:#101018;
  border:1px solid #1d1d2b;
  border-radius:16px;
  padding:20px;
}
.progress-title{
  font-size:.95rem;
  color:#d1d5db;
  margin-bottom:12px;
  word-break:break-all;
}
.progress-bar-bg{
  width:100%;
  height:9px;
  background:#1b1b25;
  border-radius:999px;
  overflow:hidden;
}
.progress-bar-fill{
  height:100%;
  width:0%;
  background:linear-gradient(90deg,#6366f1,#a855f7,#ec4899);
  border-radius:999px;
  transition:width .25s ease;
}
.progress-info{
  display:flex;
  justify-content:space-between;
  gap:10px;
  margin-top:10px;
  color:#8b8b9a;
  font-size:.82rem;
}
.result{
  display:none;
  margin-top:22px;
  background:#101018;
  border:1px solid #1d1d2b;
  border-radius:16px;
  padding:20px;
}
.result .fname{
  font-weight:700;
  color:#fff;
  word-break:break-all;
}
.result .fsize{
  color:#8b8b9a;
  font-size:.86rem;
  margin-top:5px;
}
.link-label{
  margin-top:16px;
  margin-bottom:8px;
  color:#9ca3af;
  font-size:.8rem;
}
.link-row{
  display:flex;
  gap:8px;
}
.link-row input[type=text]{
  flex:1;
  min-width:0;
  background:#08080d;
  border:1px solid #252535;
  border-radius:10px;
  padding:11px 12px;
  color:#c4b5fd;
  font-size:.84rem;
  outline:none;
}
.files-section{
  margin-top:34px;
}
.files-head{
  display:flex;
  justify-content:space-between;
  align-items:center;
  gap:12px;
  margin-bottom:14px;
}
.files-head h2{
  font-size:1.05rem;
  color:#d1d5db;
}
.file-list{
  list-style:none;
}
.file-list li{
  background:#101018;
  border:1px solid #1d1d2b;
  border-radius:14px;
  padding:14px 16px;
  margin-bottom:10px;
  display:flex;
  justify-content:space-between;
  align-items:center;
  gap:12px;
  flex-wrap:wrap;
}
.file-list .fn{
  flex:1;
  min-width:220px;
  word-break:break-all;
  color:#e5e7eb;
  font-size:.92rem;
}
.file-list .actions{
  display:flex;
  gap:10px;
  flex-wrap:wrap;
}
.file-list a{
  color:#818cf8;
  text-decoration:none;
  font-size:.84rem;
}
.file-list a:hover{
  text-decoration:underline;
}
.empty{
  color:#555;
  border:none !important;
  background:none !important;
}
.toast{
  position:fixed;
  bottom:22px;
  right:22px;
  background:#6366f1;
  color:#fff;
  padding:12px 18px;
  border-radius:12px;
  font-size:.9rem;
  display:none;
  z-index:999;
  box-shadow:0 10px 30px rgba(0,0,0,0.35);
}
.muted{color:#6b7280;font-size:.85rem}
@media (max-width:640px){
  .topbar{
    flex-direction:column;
    align-items:flex-start;
  }
  .user-box{
    width:100%;
    justify-content:space-between;
  }
}
</style>
</head>
<body>
  <div class="topbar">
    <div class="brand">☁️ My Cloud</div>
    <div class="user-box">
      <span id="authBadge" class="badge">Loading...</span>
      <span id="userBox" class="muted">Checking session...</span>
    </div>
  </div>

  <div class="container">
    <div class="hero">
      <h1>Upload files</h1>
      <p>Drag & drop or choose a file. You will get download and CDN links.</p>
    </div>

    <div class="drop-zone" id="dropZone">
      <div class="icon">📁</div>
      <p>
        Drag &amp; drop your file here<br>
        or <span class="browse" onclick="document.getElementById('fileInput').click()">browse</span>
      </p>
      <p style="margin-top:10px;font-size:.76rem;color:#555">Max 2GB • Any file type</p>
    </div>
    <input type="file" id="fileInput">

    <div class="progress-wrap" id="progressWrap">
      <div class="progress-title" id="progressText">Uploading...</div>
      <div class="progress-bar-bg">
        <div class="progress-bar-fill" id="progressBar"></div>
      </div>
      <div class="progress-info">
        <span id="progressPercent">0%</span>
        <span id="progressSize">0 MB / 0 MB</span>
      </div>
    </div>

    <div class="result" id="resultBox">
      <div class="fname" id="resName"></div>
      <div class="fsize" id="resSize"></div>

      <div class="link-label">🔗 Download Link</div>
      <div class="link-row">
        <input type="text" id="resDownload" readonly>
        <button class="btn small" onclick="copyText('resDownload')">Copy</button>
      </div>

      <div class="link-label">🌐 Inline CDN Link</div>
      <div class="link-row">
        <input type="text" id="resCdn" readonly>
        <button class="btn small" onclick="copyText('resCdn')">Copy</button>
      </div>
    </div>

    <div class="files-section">
      <div class="files-head">
        <h2>📂 Uploaded Files</h2>
        <button class="btn ghost small" onclick="loadFiles()">Refresh</button>
      </div>
      <ul class="file-list" id="fileList">
        <li class="empty">Loading...</li>
      </ul>
    </div>
  </div>

  <div class="toast" id="toast">✅ Copied!</div>

<script>
const dropZone = document.getElementById('dropZone');
const fileInput = document.getElementById('fileInput');
const progressWrap = document.getElementById('progressWrap');
const progressBar = document.getElementById('progressBar');
const progressText = document.getElementById('progressText');
const progressPercent = document.getElementById('progressPercent');
const progressSize = document.getElementById('progressSize');
const resultBox = document.getElementById('resultBox');
const resName = document.getElementById('resName');
const resSize = document.getElementById('resSize');
const resDownload = document.getElementById('resDownload');
const resCdn = document.getElementById('resCdn');
const fileList = document.getElementById('fileList');
const toast = document.getElementById('toast');
const authBadge = document.getElementById('authBadge');
const userBox = document.getElementById('userBox');

function escapeHtml(value) {
  return String(value || '').replace(/[&<>"']/g, function(ch) {
    return {
      '&': '&amp;',
      '<': '&lt;',
      '>': '&gt;',
      '"': '&quot;',
      "'": '&#39;'
    }[ch];
  });
}

function fmtBytes(bytes) {
  if (bytes < 1024) return bytes + ' B';
  if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + ' KB';
  if (bytes < 1024 * 1024 * 1024) return (bytes / (1024 * 1024)).toFixed(1) + ' MB';
  return (bytes / (1024 * 1024 * 1024)).toFixed(2) + ' GB';
}

function showToast(message) {
  toast.textContent = message;
  toast.style.display = 'block';
  setTimeout(function() {
    toast.style.display = 'none';
  }, 2000);
}

function copyText(id) {
  const el = document.getElementById(id);
  el.select();
  navigator.clipboard.writeText(el.value).then(function() {
    showToast('✅ Copied!');
  }).catch(function() {
    document.execCommand('copy');
    showToast('✅ Copied!');
  });
}

async function apiFetch(url, options) {
  options = options || {};
  options.credentials = 'same-origin';

  const res = await fetch(url, options);

  if (res.status === 401) {
    const next = encodeURIComponent(window.location.pathname + window.location.search);
    window.location.href = '/login?next=' + next;
    throw new Error('Unauthorized');
  }

  return res;
}

dropZone.addEventListener('dragover', function(e) {
  e.preventDefault();
  dropZone.classList.add('dragover');
});

dropZone.addEventListener('dragleave', function() {
  dropZone.classList.remove('dragover');
});

dropZone.addEventListener('drop', function(e) {
  e.preventDefault();
  dropZone.classList.remove('dragover');
  if (e.dataTransfer.files.length) {
    uploadFile(e.dataTransfer.files[0]);
  }
});

fileInput.addEventListener('change', function(e) {
  if (e.target.files.length) {
    uploadFile(e.target.files[0]);
  }
});

function uploadFile(file) {
  progressWrap.style.display = 'block';
  resultBox.style.display = 'none';
  progressBar.style.width = '0%';
  progressText.textContent = 'Uploading ' + file.name + '...';
  progressPercent.textContent = '0%';
  progressSize.textContent = '0 MB / ' + fmtBytes(file.size);

  const formData = new FormData();
  formData.append('file', file);

  const xhr = new XMLHttpRequest();
  xhr.open('POST', '/api/upload', true);
  xhr.withCredentials = true;

  xhr.upload.onprogress = function(e) {
    if (e.lengthComputable) {
      const pct = Math.round((e.loaded / e.total) * 100);
      progressBar.style.width = pct + '%';
      progressPercent.textContent = pct + '%';
      progressSize.textContent = fmtBytes(e.loaded) + ' / ' + fmtBytes(e.total);
    }
  };

  xhr.onload = function() {
    if (xhr.status === 200) {
      let data;
      try {
        data = JSON.parse(xhr.responseText);
      } catch (err) {
        progressWrap.style.display = 'none';
        alert('Invalid server response.');
        return;
      }

      progressWrap.style.display = 'none';
      resultBox.style.display = 'block';

      resName.textContent = '📁 ' + (data.filename || 'file');
      resSize.textContent = '📦 ' + fmtBytes(data.size || 0);
      resDownload.value = data.download_url || data.url || '';
      resCdn.value = data.cdn_url || data.url || '';

      loadFiles();
      showToast('✅ Upload complete');
    } else if (xhr.status === 401) {
      progressWrap.style.display = 'none';
      const next = encodeURIComponent(window.location.pathname + window.location.search);
      window.location.href = '/login?next=' + next;
    } else {
      progressWrap.style.display = 'none';
      let msg = 'Upload failed';
      try {
        const err = JSON.parse(xhr.responseText);
        msg = err.detail || msg;
      } catch (e) {}
      alert(msg);
    }
  };

  xhr.onerror = function() {
    progressWrap.style.display = 'none';
    alert('Network error');
  };

  xhr.send(formData);
}

async function loadMe() {
  try {
    const res = await fetch('/api/me', { credentials: 'same-origin' });
    const data = await res.json();

    if (!data.auth_enabled) {
      authBadge.textContent = 'Public mode';
      userBox.innerHTML = '<span class="muted">Authentication disabled</span>';
      return;
    }

    if (data.authenticated) {
      authBadge.textContent = 'Logged in';
      userBox.innerHTML =
        '<span>' + escapeHtml(data.username || '') + '</span>' +
        '<form method="post" action="/logout" style="display:inline">' +
        '<button class="btn small ghost" type="submit">Logout</button>' +
        '</form>';
    } else {
      window.location.href = '/login?next=%2F';
    }
  } catch (err) {
    authBadge.textContent = 'Offline?';
    userBox.innerHTML = '<span class="muted">Cannot reach server</span>';
  }
}

async function loadFiles() {
  try {
    const res = await apiFetch('/api/files');
    const data = await res.json();
    const items = data.items || [];

    if (!items.length) {
      fileList.innerHTML = '<li class="empty">No files yet</li>';
      return;
    }

    fileList.innerHTML = items.map(function(item) {
      const downloadUrl = item.download_url || ('/download/' + encodeURIComponent(item.name));
      const cdnUrl = item.cdn_url || ('/cdn/' + encodeURIComponent(item.name));

      return '<li>' +
        '<span class="fn">' + escapeHtml(item.name) + '</span>' +
        '<span class="actions">' +
          '<a href="' + escapeHtml(downloadUrl) + '" target="_blank" rel="noopener">⬇ Download</a>' +
          '<a href="' + escapeHtml(cdnUrl) + '" target="_blank" rel="noopener">🌐 Open</a>' +
        '</span>' +
      '</li>';
    }).join('');
  } catch (err) {
    fileList.innerHTML = '<li class="empty">Failed to load files</li>';
  }
}

loadMe();
loadFiles();
</script>
</body>
</html>"""


def render_login(error: str = "", next_url: str = "/") -> str:
    error_html = ""
    if error:
        error_html = f'<div class="error">{html_lib.escape(error)}</div>'

    return (
        LOGIN_TEMPLATE
        .replace("%%ERROR%%", error_html)
        .replace("%%NEXT%%", html_lib.escape(safe_next_url(next_url), quote=True))
    )


# ══════════════════════════════════════════════════════════════
# Auth guards
# ══════════════════════════════════════════════════════════════
def ensure_login_api(request: Request) -> str:
    if not AUTH_ENABLED:
        return "anonymous"

    user = get_current_user(request)
    if not user:
        raise HTTPException(status_code=401, detail="Login required")

    return user


def download_guard(request: Request):
    if not (PROTECT_DOWNLOADS and AUTH_ENABLED):
        return None

    user = get_current_user(request)
    if user:
        return None

    next_url = quote(request.url.path, safe="/")
    return RedirectResponse(f"/login?next={next_url}", status_code=302)


# ══════════════════════════════════════════════════════════════
# Web routes
# ══════════════════════════════════════════════════════════════
@app.get("/", response_class=HTMLResponse)
def dashboard(request: Request):
    if AUTH_ENABLED and not get_current_user(request):
        return RedirectResponse("/login?next=%2F", status_code=302)

    return HTMLResponse(DASHBOARD_HTML)


@app.get("/login", response_class=HTMLResponse)
def login_page(request: Request, next: str = "/"):
    if not AUTH_ENABLED:
        return RedirectResponse("/", status_code=302)

    user = get_current_user(request)
    if user:
        return RedirectResponse(safe_next_url(next), status_code=302)

    return HTMLResponse(render_login("", next))


@app.post("/login", response_class=HTMLResponse)
async def login_submit(
    request: Request,
    username: str = Form(default=""),
    password: str = Form(default=""),
    next: str = Form(default="/"),
):
    """Handle login form submission."""
    if not AUTH_ENABLED:
        return RedirectResponse("/", status_code=302)

    purge_failed_attempts()

    # Validate credentials
    username = (username or "").strip()
    # NOTE: never strip the password — leading/trailing spaces may be intentional
    password = password or ""
    next = (next or "/").strip()

    # Key lockouts by username too — on Hugging Face Spaces request.client.host
    # is an internal proxy IP (10.16.x.x), so IP-only keys are unreliable.
    ip = request.client.host if request.client else "unknown"
    attempt_key = f"{ip}|{username}"
    now = time.time()
    record = failed_attempts.get(attempt_key)

    if record and record[1] > now:
        return HTMLResponse(
            render_login("Too many failed attempts. Please try again later.", next),
            status_code=429,
        )

    if record and record[1] and record[1] <= now:
        failed_attempts.pop(attempt_key, None)
        record = None

    if username == ADMIN_USERNAME and password and verify_password(password, PASSWORD_HASH):
        failed_attempts.pop(attempt_key, None)

        token = create_session_token(username)
        redirect = RedirectResponse(safe_next_url(next), status_code=302)
        redirect.set_cookie(
            key=COOKIE_NAME,
            value=token,
            max_age=SESSION_MAX_AGE,
            httponly=True,
            samesite="lax",
            secure=is_https_request(request),
            path="/",
        )

        logger.info(f"✅ Login success: {username} from {ip}")
        return redirect

    fail_count = (record[0] + 1) if record else 1
    locked_until = now + LOCK_SECONDS if fail_count >= MAX_FAILED_ATTEMPTS else 0
    failed_attempts[attempt_key] = (fail_count, locked_until)

    logger.warning(f"⚠️ Failed login attempt from {ip}: {fail_count}")

    return HTMLResponse(
        render_login("Invalid username or password", next),
        status_code=401,
    )


@app.post("/logout")
def logout(request: Request):
    redirect = RedirectResponse("/", status_code=302)
    redirect.delete_cookie(
        key=COOKIE_NAME,
        path="/",
    )
    return redirect


HEALTH_HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<meta http-equiv="refresh" content="15">
<title>Health - My Cloud</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{
  font-family:'Segoe UI',system-ui,-apple-system,sans-serif;
  background:#0a0a0f;
  color:#e0e0e0;
  min-height:100vh;
  display:flex;
  align-items:center;
  justify-content:center;
  padding:20px;
}
.card{
  width:100%;
  max-width:560px;
  background:#12121a;
  border:1px solid #23233a;
  border-radius:18px;
  padding:28px;
  box-shadow:0 20px 60px rgba(0,0,0,0.4);
}
h1{
  font-size:1.5rem;
  margin-bottom:20px;
  background:linear-gradient(135deg,#6366f1,#a855f7,#ec4899);
  -webkit-background-clip:text;
  -webkit-text-fill-color:transparent;
}
table{width:100%;border-collapse:collapse}
td{
  padding:11px 8px;
  border-bottom:1px solid #1b1b28;
  font-size:.92rem;
  vertical-align:top;
}
td.k{color:#8b8b9a;width:45%}
td.v{color:#e5e7eb;word-break:break-all}
.ok{color:#34d399;font-weight:600}
.bad{color:#f87171;font-weight:600}
.warn{color:#fbbf24;font-weight:600}
.muted{color:#555;font-size:.78rem;margin-top:16px;text-align:center}
a{color:#818cf8;text-decoration:none}
a:hover{text-decoration:underline}
</style>
</head>
<body>
  <div class="card">
    <h1>☁️ My Cloud &mdash; Health</h1>
    <table>%%ROWS%%</table>
    <div class="muted">Auto-refreshes every 15s &bull; <a href="/">Back to dashboard</a></div>
  </div>
</body>
</html>"""


def _health_bool(ok: bool, ok_text: str = "OK", bad_text: str = "FAILING"):
    cls = "ok" if ok else "bad"
    mark = "✅" if ok else "❌"
    return f'<span class="{cls}">{mark} {ok_text if ok else bad_text}</span>'


@app.get("/health")
def health(request: Request):
    """Public health endpoint. HTML page for browsers, JSON for API clients."""
    diagnostics = {
        "status": "ok",
        "time": datetime.utcnow().isoformat(),
        "repo": HF_REPO or None,
        "hf_configured": bool(hf_api),
        "public_base_url": PUBLIC_BASE_URL or None,
        "auth_enabled": AUTH_ENABLED,
        "protect_downloads_effective": bool(PROTECT_DOWNLOADS and AUTH_ENABLED),
        "telegram_ok": TELEGRAM_OK,
        "debug_errors": DEBUG_ERRORS,
        "python": sys.version.split()[0],
    }
    if DEBUG_ERRORS:
        diagnostics["telegram_error"] = TELEGRAM_ERROR
        diagnostics["startup_error"] = STARTUP_ERROR

    accept = request.headers.get("accept", "")
    wants_json = "application/json" in accept and "text/html" not in accept
    if wants_json or request.url.query.endswith("format=json"):
        return JSONResponse(diagnostics)

    rows = [
        ("Status", '<span class="ok">🟢 Running</span>'),
        ("Time (UTC)", html_lib.escape(str(diagnostics["time"]))),
        ("HF Dataset Repo", html_lib.escape(str(diagnostics["repo"]))),
        ("HF Token configured", _health_bool(diagnostics["hf_configured"], "Yes", "No — set HF_TOKEN")),
        ("Public base URL", html_lib.escape(str(diagnostics["public_base_url"]))),
        ("Web auth", _health_bool(diagnostics["auth_enabled"], "Enabled", "Disabled")),
        ("Protected downloads", _health_bool(
            diagnostics["protect_downloads_effective"],
            "Enabled", "Not effective (needs auth + PROTECT_DOWNLOADS)")),
        ("Telegram bot", _health_bool(diagnostics["telegram_ok"], "Connected", "Not connected")),
    ]
    if DEBUG_ERRORS:
        rows.append(("Telegram error", f'<span class="bad">{html_lib.escape(str(TELEGRAM_ERROR))}</span>'))
        if STARTUP_ERROR:
            rows.append(("Startup error", f'<span class="bad">{html_lib.escape(str(STARTUP_ERROR))}</span>'))
    rows.append(("Debug errors", _health_bool(DEBUG_ERRORS, "On (stack traces shown)", "Off")))
    rows.append(("Python", html_lib.escape(diagnostics["python"])))

    rows_html = "".join(
        f"<tr><td class='k'>{k}</td><td class='v'>{v}</td></tr>" for k, v in rows
    )
    return HTMLResponse(HEALTH_HTML_TEMPLATE.replace("%%ROWS%%", rows_html))


@app.get("/api/me")
def api_me(request: Request):
    user = get_current_user(request)

    return {
        "auth_enabled": AUTH_ENABLED,
        "authenticated": bool(user) if AUTH_ENABLED else True,
        "username": user or ("anonymous" if not AUTH_ENABLED else None),
        "protect_downloads": bool(PROTECT_DOWNLOADS and AUTH_ENABLED),
        "public_base_url": PUBLIC_BASE_URL or None,
    }


# ══════════════════════════════════════════════════════════════
# File API
# ══════════════════════════════════════════════════════════════
@app.get("/api/files")
def api_files(request: Request):
    ensure_login_api(request)

    if not hf_api:
        return {
            "files": [],
            "items": [],
            "count": 0,
            "error": "HF_TOKEN not configured",
        }

    try:
        raw = hf_api.list_repo_files(repo_id=HF_REPO, repo_type="dataset")

        skip = {".gitattributes", "README.md", ".gitignore"}
        files = [
            f
            for f in raw
            if f not in skip and not f.startswith(".")
        ]

        items = []

        for f in files:
            try:
                items.append(
                    {
                        "name": f,
                        "download_url": build_download_url(f),
                        "cdn_url": build_cdn_url(f),
                    }
                )
            except HTTPException:
                continue

        return {
            "files": files,
            "items": items,
            "count": len(files),
        }

    except Exception as e:
        logger.error(f"❌ List failed: {e}")
        return {
            "files": [],
            "items": [],
            "count": 0,
            "error": str(e),
        }


@app.post("/api/upload")
async def api_upload(request: Request, file: UploadFile = File(...)):
    ensure_login_api(request)

    if not hf_api:
        raise HTTPException(status_code=500, detail="HF_TOKEN not configured")

    original_name = file.filename or ""
    filename = Path(original_name).name

    if not filename:
        filename = f"file_{uuid.uuid4().hex[:8]}"

    try:
        safe_filename = safe_relative_path(filename)
    except HTTPException:
        safe_filename = f"file_{uuid.uuid4().hex[:8]}"

    tmp_path = TMP_DIR / f"{uuid.uuid4().hex}_{safe_filename}"
    size = 0

    try:
        async with aiofiles.open(tmp_path, "wb") as out:
            while chunk := await file.read(8 * 1024 * 1024):
                size += len(chunk)

                if size > MAX_FILE_SIZE:
                    raise HTTPException(
                        status_code=413,
                        detail="File too large",
                    )

                await out.write(chunk)

        logger.info(
            f"🌐 Web upload: {safe_filename} ({size / (1024 * 1024):.1f} MB)"
        )

        await asyncio.to_thread(
            hf_api.upload_file,
            path_or_fileobj=str(tmp_path),
            path_in_repo=safe_filename,
            repo_id=HF_REPO,
            repo_type="dataset",
            commit_message=f"Web upload: {safe_filename}",
        )

        download_url = build_download_url(safe_filename, request)
        cdn_url = build_cdn_url(safe_filename, request)

        return {
            "success": True,
            "filename": safe_filename,
            "size": size,
            "url": download_url,
            "download_url": download_url,
            "cdn_url": cdn_url,
        }

    except HTTPException:
        raise

    except Exception as e:
        logger.error(f"❌ Web upload failed: {e}")
        raise HTTPException(status_code=500, detail=str(e))

    finally:
        try:
            tmp_path.unlink(missing_ok=True)
        except Exception:
            pass


# ══════════════════════════════════════════════════════════════
# CDN / Download endpoints
# ══════════════════════════════════════════════════════════════
@app.get("/cdn/{filename:path}")
def cdn_redirect(request: Request, filename: str):
    guard = download_guard(request)
    if guard:
        return guard

    return RedirectResponse(
        direct_hf_url(filename, download=False),
        status_code=302,
    )


@app.get("/download/{filename:path}")
def download_file(request: Request, filename: str):
    guard = download_guard(request)
    if guard:
        return guard

    return RedirectResponse(
        direct_hf_url(filename, download=True),
        status_code=302,
    )


# ══════════════════════════════════════════════════════════════
# Telegram -> HuggingFace TRUE STREAMING (zero disk usage)
# Chunks are pulled from Telethon on the client event loop and fed
# directly into huggingface_hub's multipart upload in a worker thread.
# ══════════════════════════════════════════════════════════════
class TelegramStreamReader:
    """
    Synchronous file-like object that streams chunks from a Telethon async
    iterator into a blocking reader. huggingface_hub passes this to
    requests-toolbelt's MultipartEncoder, which reads it lazily — so only a
    small buffer lives in RAM and nothing is written to disk.

    read() is called from a worker thread; it schedules __anext__() on the
    Telethon client event loop and blocks until the chunk arrives (natural
    backpressure — Telegram only downloads as fast as HF consumes).
    """

    def __init__(self, aiter, total_size: int, loop, read_chunk: int = 1024 * 1024):
        self._aiter = aiter
        self._total = int(total_size)
        self._loop = loop
        self._read_chunk = read_chunk
        self._buf = b""
        self._done = False
        self.bytes_served = 0

    # requests-toolbelt uses len(obj) for the Content-Length header
    def __len__(self):
        return self._total

    def readable(self) -> bool:
        return True

    def read(self, n: int = -1) -> bytes:
        try:
            want = n if (n is not None and n > 0) else self._read_chunk
            while not self._done and len(self._buf) < want:
                try:
                    fut = asyncio.run_coroutine_threadsafe(
                        self._aiter.__anext__(), self._loop
                    )
                    self._buf += fut.result()
                except StopAsyncIteration:
                    self._done = True

            if n is None or n < 0:
                out, self._buf = self._buf, b""
            else:
                out, self._buf = self._buf[:n], self._buf[n:]

            self.bytes_served += len(out)
            return out
        except Exception:
            self._done = True
            raise


async def tg_fallback_disk_upload(event, msg, fname: str) -> None:
    """Fallback: download to the RAM disk, then upload (old behaviour)."""
    file_path = None

    try:
        last_pct = 0

        def progress(cur, tot):
            nonlocal last_pct

            if not tot:
                return

            pct = int((cur / tot) * 100)

            if pct >= last_pct + 10:
                last_pct = pct
                asyncio.create_task(
                    msg.edit(
                        f"📥 *Downloading:* `{fname}`\n⏳ {pct}%",
                        parse_mode="markdown",
                    )
                )

        result = await client.download_media(
            event.message,
            progress_callback=progress,
        )

        if result is None:
            raise Exception("Download returned None")

        if isinstance(result, bytes):
            tmp_file = TMP_DIR / f"{uuid.uuid4().hex}_{fname}"
            tmp_file.write_bytes(result)
            file_path = str(tmp_file)
        else:
            file_path = str(result)

        size_mb = os.path.getsize(file_path) / (1024 * 1024)

        await msg.edit(
            f"📤 *Uploading {size_mb:.1f} MB to Cloud...*",
            parse_mode="markdown",
        )

        await asyncio.to_thread(
            hf_api.upload_file,
            path_or_fileobj=file_path,
            path_in_repo=fname,
            repo_id=HF_REPO,
            repo_type="dataset",
            commit_message=f"TG upload: {fname}",
        )

        download_link = build_download_url(fname)
        cdn_link = build_cdn_url(fname)

        await msg.edit(
            "✅ *Done!* (fallback mode)\n\n"
            f"📁 `{fname}`\n"
            f"📦 {size_mb:.2f} MB\n\n"
            f"🔗 *Download:*\n{download_link}\n\n"
            f"🌐 *Inline CDN:*\n{cdn_link}",
            parse_mode="markdown",
        )

        logger.info(f"✅ TG upload OK (fallback): {fname}")

    finally:
        if file_path:
            try:
                Path(file_path).unlink(missing_ok=True)
            except Exception:
                pass


# ══════════════════════════════════════════════════════════════
# Telegram Bot (Non-fatal startup)
# ══════════════════════════════════════════════════════════════
async def start_telegram():
    """Start Telegram bot in background. Non-fatal if it fails."""
    global TELEGRAM_OK, TELEGRAM_ERROR

    if not client:
        logger.warning("⚠️ Telegram client not configured (missing TG_API_ID or TG_API_HASH)")
        TELEGRAM_ERROR = "Client not configured"
        return

    try:
        await client.start(bot_token=BOT_TOKEN)
        TELEGRAM_OK = True
        logger.info("✅ Telegram bot connected")
    except Exception as e:
        TELEGRAM_OK = False
        TELEGRAM_ERROR = str(e)
        logger.error(f"❌ Telegram startup failed: {e}")
        # Don't re-raise; let FastAPI continue


@client.on(events.NewMessage(pattern="/start"))
async def tg_start(event):
    if PUBLIC_BASE_URL:
        web_line = f"\n\n☁️ Web: {PUBLIC_BASE_URL}"
    else:
        web_line = (
            "\n\n⚙️ Set PUBLIC_BASE_URL secret "
            "to enable your own domain links."
        )

    await event.reply(
        "👋 *My Cloud Bot*\n\n"
        "Send me any file and I'll give you a download link.\n"
        f"{web_line}",
        parse_mode="markdown",
    )


@client.on(events.NewMessage(pattern="/files"))
async def tg_files(event):
    if not hf_api:
        await event.reply("❌ HuggingFace not configured")
        return

    try:
        raw = hf_api.list_repo_files(repo_id=HF_REPO, repo_type="dataset")

        skip = {".gitattributes", "README.md", ".gitignore"}
        files = [
            f
            for f in raw
            if f not in skip and not f.startswith(".")
        ]

        if not files:
            await event.reply("📂 No files uploaded yet.")
            return

        lines = "\n".join(f"• {f}" for f in files[:50])

        await event.reply(
            f"📂 *Files ({len(files)}):*\n{lines}",
            parse_mode="markdown",
        )

    except Exception as e:
        await event.reply(f"❌ Error: {e}")


@client.on(events.NewMessage())
async def tg_handle_file(event):
    if not hf_api:
        return

    if event.message.text and event.message.text.startswith("/"):
        return

    if not event.message.file:
        return

    msg = await event.reply("📥 *Preparing...*", parse_mode="markdown")

    raw_name = getattr(event.message.file, "name", None)
    fname = Path(raw_name).name if raw_name else ""

    if not fname:
        if getattr(event.message, "photo", None):
            ext = ".jpg"
        else:
            ext = getattr(event.message.file, "ext", None) or ".bin"
            if not ext.startswith("."):
                ext = f".{ext}"

        fname = f"tg_{event.message.id}{ext}"

    try:
        fname = safe_relative_path(fname)
    except HTTPException:
        fname = f"tg_{event.message.id}.bin"

    total_size = int(getattr(event.message.file, "size", 0) or 0)

    # ── Path 1 (preferred): TRUE streaming — Telegram -> HF, zero disk ──
    streamed = False
    try:
        if total_size <= 0:
            raise ValueError("unknown file size")

        loop = asyncio.get_running_loop()
        aiter = client.iter_download(event.message.media, chunk_size=512 * 1024)
        stream = TelegramStreamReader(aiter, total_size, loop)

        async def report_progress():
            try:
                last = -1
                while stream.bytes_served < total_size:
                    await asyncio.sleep(2)
                    pct = int(stream.bytes_served * 100 / total_size)
                    if pct != last and pct < 100:
                        last = pct
                        await msg.edit(
                            "🚀 *Streaming to HF...*\n"
                            f"📁 `{fname}`\n"
                            f"⏳ {pct}% "
                            f"({stream.bytes_served / (1024 * 1024):.1f} / "
                            f"{total_size / (1024 * 1024):.1f} MB)",
                            parse_mode="markdown",
                        )
            except asyncio.CancelledError:
                pass
            except Exception:
                pass

        progress_task = asyncio.create_task(report_progress())

        try:
            await asyncio.to_thread(
                hf_api.upload_file,
                path_or_fileobj=stream,
                path_in_repo=fname,
                repo_id=HF_REPO,
                repo_type="dataset",
                commit_message=f"TG stream upload: {fname}",
            )
        finally:
            progress_task.cancel()

        streamed = True
        size_mb = total_size / (1024 * 1024)
        download_link = build_download_url(fname)
        cdn_link = build_cdn_url(fname)

        await msg.edit(
            "✅ *Done!* (streamed, no disk used)\n\n"
            f"📁 `{fname}`\n"
            f"📦 {size_mb:.2f} MB\n\n"
            f"🔗 *Download:*\n{download_link}\n\n"
            f"🌐 *Inline CDN:*\n{cdn_link}",
            parse_mode="markdown",
        )

        logger.info(f"✅ TG stream upload OK: {fname} ({size_mb:.1f} MB)")

    except Exception as e:
        logger.warning(f"⚠️ Streaming upload failed ({type(e).__name__}: {e}); "
                       f"falling back to RAM-disk download")

    # ── Path 2 (fallback): RAM-disk download then upload ──
    if not streamed:
        try:
            await tg_fallback_disk_upload(event, msg, fname)
        except Exception as e:
            logger.error(f"❌ TG upload failed: {e}")
            await msg.edit(
                f"❌ `{type(e).__name__}: {str(e)[:200]}`",
                parse_mode="markdown",
            )


# ══════════════════════════════════════════════════════════════
# Startup / Shutdown
# ══════════════════════════════════════════════════════════════
@app.on_event("startup")
async def on_startup():
    global STARTUP_ERROR

    logger.info("🚀 Starting My Cloud...")

    if PUBLIC_BASE_URL:
        logger.info(f"PUBLIC_BASE_URL = {PUBLIC_BASE_URL}")
    else:
        logger.warning(
            "PUBLIC_BASE_URL is not set. "
            "Web links will use request host when possible. "
            "Telegram links will fallback to direct Hugging Face URLs."
        )

    if AUTH_ENABLED:
        logger.info("✅ Web auth enabled")
    else:
        logger.warning("⚠️ Web auth disabled")

    if DEBUG_ERRORS:
        logger.info("🐛 DEBUG_ERRORS enabled - will show stack traces in /health")

    # Start Telegram in background (non-fatal)
    try:
        asyncio.create_task(start_telegram())
    except Exception as e:
        STARTUP_ERROR = str(e)
        logger.error(f"❌ Failed to create Telegram startup task: {e}")


@app.on_event("shutdown")
async def on_shutdown():
    if client:
        try:
            await client.disconnect()
            logger.info("🛑 Bot disconnected")
        except Exception as e:
            logger.warning(f"⚠️ Error disconnecting bot: {e}")


if __name__ == "__main__":
    import uvicorn

    uvicorn.run(
        app,
        host="0.0.0.0",
        port=int(os.getenv("PORT", "7860")),
        reload=False,
    )
