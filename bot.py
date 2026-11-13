"""
Free Fire Info Bot (Telegram)
  /info <uid>  |  info <uid>  |  /get <uid>  |  get <uid>  |  uid <uid>
  /item <item id or name>
  /track <uid>  (private chat only: instant alerts when anything on that profile changes)

Every value is wrapped in <code> so a single tap copies it.
Single file: missing packages are installed automatically on first run.
Env vars: BOT_TOKEN (required), INFO_API, ITEM_API, WATERMARK, FONT_PATH, PORT (Render keep-alive),
          TRACK_MIN, TRACK_MAX, MAX_TRACKS_PER_USER (default 2), MAX_TRACKS_TOTAL, DATA_DIR,
          OWNER_ID (default 8536757095), MONGO_URI + MONGO_DB (optional: settings & tracking backup), see db.py
"""
import os
import subprocess
import sys


def _ensure(mod, pkg, required=True):
    try:
        __import__(mod)
    except ImportError:
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", pkg])
        except Exception as e:
            if required:
                raise SystemExit(f"Could not install {pkg}: {e}")


_ensure("telegram", "python-telegram-bot>=21,<23")
_ensure("httpx", "httpx")
_ensure("PIL", "Pillow", required=False)
if os.getenv("MONGO_URI"):  # optional: keeps /track data across restarts
    _ensure("motor", "motor", required=False)
    _ensure("dns", "dnspython", required=False)

import asyncio
import html
import io
import json
import logging
import os
import re
import random
import threading
import time
import urllib.request
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer

import httpx

import db  # permanent storage (data/ffbot.db) - keep db.py next to this file
from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, Update
from telegram.constants import ChatAction, ChatType, ParseMode
from telegram.error import Forbidden, RetryAfter, TimedOut
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

try:
    from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageFont, ImageOps

    PIL_OK = True
except ImportError:  # images are optional
    PIL_OK = False

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("ffinfo")

BOT_TOKEN = os.getenv("BOT_TOKEN", "")
INFO_API = os.getenv("INFO_API", "https://rosyyinfo.vercel.app/info")
ITEM_API = os.getenv("ITEM_API", "https://starexx.vercel.app/api/items")
WATERMARK = os.getenv("WATERMARK", "SK")
# Icon CDNs (PNG first; WEBP is converted with Pillow)
ICON_URLS = [
    "https://cdn.jsdelivr.net/gh/ShahGCreator/icon@main/PNG/{id}.png",
    "https://cdn.jsdelivr.net/gh/AfnanTawsif/ff-catalog@main/Item-webp/{id}.webp",
]
FONT_URLS = [
    "https://cdn.jsdelivr.net/npm/dejavu-fonts-ttf@2.37.3/ttf/DejaVuSans-Bold.ttf",
    "https://cdn.jsdelivr.net/gh/dejavu-fonts/dejavu-fonts@version_2_37/ttf/DejaVuSans-Bold.ttf",
]

IST = timezone(timedelta(hours=5, minutes=30))
CACHE_TTL = 60       # player cache, seconds
ITEM_TTL = 6 * 3600  # item cache, seconds
COOLDOWN = 3         # per user, seconds
MAX_LEN = 3800       # Telegram limit is 4096 (room left for the frame)
TO = dict(read_timeout=60, write_timeout=60, connect_timeout=20, pool_timeout=20)  # uploads need >5s

PLAYER_CACHE: dict = {}
ITEM_CACHE: dict = {}
LAST_USE: dict = {}
SEEN: dict = {}
_client = None


def trim(d: dict, limit: int):
    """Keep a cache dict from growing forever (drops the oldest quarter)."""
    if len(d) > limit:
        for k in list(d)[: max(1, limit // 4)]:
            d.pop(k, None)


# ───────────────────────── text helpers ─────────────────────────
_FX = str.maketrans({"a": "α", "k": "к", "r": "ʀ"})


def fx(s) -> str:
    """Label font: Pαcкʀʀ style."""
    return str(s).translate(_FX)


def http() -> httpx.AsyncClient:
    global _client
    if _client is None:
        _client = httpx.AsyncClient(
            timeout=20, follow_redirects=True, headers={"User-Agent": "Mozilla/5.0"}
        )
    return _client


def esc(v) -> str:
    return html.escape(str(v), quote=False)


def cp(v) -> str:
    """Tap-to-copy value."""
    s = "" if v is None else str(v)
    return f"<code>{esc(s if s != '' else '—')}</code>"


_TAG = re.compile(r"\[(?:/?[A-Za-z]{1,2}|[0-9A-Fa-f]{6,8})\]")


def clean(s) -> str:
    return _TAG.sub("", str(s or "")).strip()


def indian(n) -> str:
    try:
        s = str(int(n))
    except Exception:
        return str(n)
    neg = s.startswith("-")
    s = s.lstrip("-")
    if len(s) > 3:
        head, tail = s[:-3], s[-3:]
        parts = []
        while len(head) > 2:
            parts.insert(0, head[-2:])
            head = head[:-2]
        if head:
            parts.insert(0, head)
        s = ",".join(parts + [tail])
    return ("-" if neg else "") + s


def ts(t) -> str:
    try:
        t = int(t)
        if t <= 0:
            return "0"
        return datetime.fromtimestamp(t, IST).strftime("%d %b %Y, %I:%M %p")
    except Exception:
        return str(t)


def enum_txt(s, prefix="") -> str:
    return str(s).replace(prefix, "").replace("_", " ").title()


# Approximate BR tier names (API only returns a numeric code) - edit if needed
def br_rank(code) -> str:
    try:
        c = int(code)
    except Exception:
        return ""
    names = []
    for tier, n in (("Bronze", 3), ("Silver", 3), ("Gold", 4), ("Platinum", 4), ("Diamond", 4)):
        names += [f"{tier} {'I' * i if i < 4 else 'IV'}" for i in range(1, n + 1)]
    names += ["Heroic", "Elite Heroic", "Master", "Grandmaster"]
    idx = c - 301
    return names[idx] if 0 <= idx < len(names) else ""


def fail_text(e) -> str:
    """What the USER sees when a lookup fails (no technical codes)."""
    if isinstance(e, (httpx.HTTPStatusError, ValueError)):
        return "Player not found. Please check the UID and try again."
    return "The server is not responding right now. Please try again in a moment."


def why(e) -> str:
    """Short failure reason for the user."""
    if isinstance(e, httpx.HTTPStatusError):
        return f"HTTP {e.response.status_code}"
    if isinstance(e, httpx.TimeoutException):
        return "timeout"
    if isinstance(e, ValueError):
        return "no data"
    return type(e).__name__


# rows: (label, html value)
def R(label, value, name="", fmt=None):
    shown = fmt(value) if fmt else value
    v = cp(shown)
    if name:
        v += f" → {esc(name)}"
    return (fx(label), v)


def B(label, value):
    return (fx(label), "Yes" if value else "No")


def E(label, value):
    return (fx(label), "Equipped" if value else "Not Equipped")


def L(label, items):
    """items: list of ready html strings"""
    if not items:
        return (fx(label), cp("[]"))
    return (fx(label), "".join(f"\n│    • {x}" for x in items))


def id_line(i, nm):
    n = nm.get(str(i), "")
    return cp(i) + (f" → {esc(n)}" if n else "")


def section(title, rows) -> str:
    out = [f"<b>{fx(title)}</b>"]
    for i, (lab, val) in enumerate(rows):
        pre = "└" if i == len(rows) - 1 else "├"
        out.append(f"{pre} {lab}: {val}")
    return "\n".join(out)


def pack(sections, limit=MAX_LEN):
    msgs, cur = [], ""
    for s in sections:
        chunks = [s]
        if len(s) > limit:
            chunks, buf = [], ""
            for line in s.split("\n"):
                if len(buf) + len(line) + 1 > limit:
                    chunks.append(buf)
                    buf = line
                else:
                    buf = f"{buf}\n{line}" if buf else line
            if buf:
                chunks.append(buf)
        for c in chunks:
            if cur and len(cur) + len(c) + 2 > limit:
                msgs.append(cur)
                cur = c
            else:
                cur = f"{cur}\n\n{c}" if cur else c
    if cur:
        msgs.append(cur)
    return msgs


# ───────────────────────── "add me to your group" button under every message ─────────────────────────
BOT_USER = ""


def with_add(kb=None):
    """Existing inline keyboard (if any) + one long 'Add me to your group' button."""
    rows = [list(r) for r in kb.inline_keyboard] if kb else []
    if BOT_USER:
        rows.append([InlineKeyboardButton("Add me to your group", url=f"https://t.me/{BOT_USER}?startgroup=true")])
    return InlineKeyboardMarkup(rows) if rows else None


async def rt(msg, text, add=True, **kw):
    if kw.get("parse_mode") != ParseMode.HTML:  # plain text -> safe HTML
        text, kw["parse_mode"] = esc(text), ParseMode.HTML
    if not text.lstrip().startswith("<blockquote"):
        text = bq(text)
    if add:
        kw["reply_markup"] = with_add(kw.get("reply_markup"))
    return await msg.reply_text(text, **kw)


async def rp(msg, photo, add=True, **kw):
    cap = kw.get("caption")
    if cap and kw.get("parse_mode") == ParseMode.HTML and not cap.lstrip().startswith("<blockquote"):
        kw["caption"] = bq(cap)
    if add:
        kw["reply_markup"] = with_add(kw.get("reply_markup"))
    return await msg.reply_photo(photo, **kw)


# ───────────────────────── item db ─────────────────────────
def _pick(d, *keys, default=""):
    for k in keys:
        if k in d and d[k] not in (None, ""):
            return d[k]
    return default


def _extract_items(js):
    if isinstance(js, list):
        return [x for x in js if isinstance(x, dict)]
    if isinstance(js, dict):
        for k in ("items", "data", "results", "result"):
            v = js.get(k)
            if isinstance(v, list):
                return [x for x in v if isinstance(x, dict)]
            if isinstance(v, dict):
                return _extract_items(v)
        if any(k in js for k in ("itemID", "item_id", "id", "name")):
            return [js]
    return []


def _norm_item(d):
    return {
        "id": str(_pick(d, "itemID", "item_id", "ItemID", "id", "ID")),
        "name": str(_pick(d, "name", "Name", "itemName")),
        "desc": str(_pick(d, "description", "desc", "Description")),
        "icon": str(_pick(d, "icon", "iconName", "icon_name", "IconName")),
        "type": str(_pick(d, "type", "itemType", "Type")),
        "rarity": str(_pick(d, "rarity", "Rarity")),
    }


async def search_items(q):
    r = await http().get(ITEM_API, params={"raw": q}, timeout=10)
    r.raise_for_status()
    return [_norm_item(x) for x in _extract_items(r.json())]


async def get_item(item_id):
    key = str(item_id)
    hit = ITEM_CACHE.get(key)
    if hit and time.time() - hit[0] < ITEM_TTL:
        return hit[1]
    res = None
    try:
        for it in await search_items(key):
            if it["id"] == key:
                res = it
                break
    except Exception as e:
        log.warning("item lookup failed %s: %r", key, e)
        return None  # failures are not cached
    ITEM_CACHE[key] = (time.time(), res)
    trim(ITEM_CACHE, 4000)
    return res


async def resolve_names(ids):
    async def one(i):
        it = await get_item(i)
        return str(i), (it or {}).get("name", "")

    try:
        res = await asyncio.wait_for(
            asyncio.gather(*[one(i) for i in ids], return_exceptions=True), timeout=8
        )
    except Exception:
        return {}
    return {k: v for k, v in (r for r in res if isinstance(r, tuple)) if v}


async def fetch_icon(item_id):
    """Item icon as PNG/JPEG bytes (WEBP is converted)."""
    for tpl in ICON_URLS:
        try:
            r = await http().get(tpl.format(id=item_id), timeout=8)
            if r.status_code != 200 or len(r.content) < 300:
                continue
            data = r.content
            if data[:4] == b"RIFF":  # webp -> png
                if not PIL_OK:
                    continue
                buf = io.BytesIO()
                Image.open(io.BytesIO(data)).convert("RGBA").save(buf, "PNG")
                data = buf.getvalue()
            return data
        except Exception:
            continue
    return None


# ───────────────────────── image cards (Pillow) ─────────────────────────
FONT_PATHS = [
    p
    for p in (
        os.getenv("FONT_PATH", ""),
        "DejaVuSans-Bold.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
        "/data/data/com.termux/files/usr/share/fonts/TTF/DejaVuSans-Bold.ttf",
        "/system/fonts/Roboto-Bold.ttf",
        "/system/fonts/NotoSansCJK-Bold.ttc",
        "/system/fonts/NotoSansCJK-Regular.ttc",
        "/system/fonts/DroidSansFallback.ttf",
        "/system/fonts/NotoSansSymbols-Regular-Subtitle.ttf",
        "/usr/share/fonts/truetype/freefont/FreeSansBold.ttf",
    )
    if p
]
_FONT_CACHE: dict = {}
_GLYPH_CACHE: dict = {}


def ensure_font():
    """If no usable font exists, fetch DejaVu Sans Bold once."""
    if not PIL_OK or any(os.path.exists(p) for p in FONT_PATHS):
        return
    for url in FONT_URLS:
        try:
            with urllib.request.urlopen(url, timeout=20) as r:
                data = r.read()
            if len(data) > 50000:
                with open("DejaVuSans-Bold.ttf", "wb") as f:
                    f.write(data)
                log.info("Font downloaded")
                return
        except Exception as e:
            log.warning("font download failed: %r", e)


def _fonts(size):
    if size in _FONT_CACHE:
        return _FONT_CACHE[size]
    fonts = []
    for p in FONT_PATHS:
        if os.path.exists(p):
            try:
                fonts.append(ImageFont.truetype(p, size))
            except Exception:
                pass
    if not fonts:
        try:
            fonts = [ImageFont.load_default(size)]
        except TypeError:
            fonts = [ImageFont.load_default()]
    _FONT_CACHE[size] = fonts
    return fonts


def _has(font, ch) -> bool:
    key = (id(font), ch)
    if key not in _GLYPH_CACHE:
        try:
            m, nd = font.getmask(ch), font.getmask("￿")
            _GLYPH_CACHE[key] = m.getbbox() is not None and (m.size, m.tobytes()) != (nd.size, nd.tobytes())
        except Exception:
            _GLYPH_CACHE[key] = True
    return _GLYPH_CACHE[key]


def _font_for(fonts, ch):
    if len(fonts) == 1 or ch.isspace():
        return fonts[0]
    for f in fonts:
        if _has(f, ch):
            return f
    return fonts[0]


_BLANK = {0x3164: " ", 0x2800: " ", 0x200B: None, 0x200E: None, 0x200F: None, 0x2060: None, 0xFEFF: None}


def _vis(text) -> str:
    return str(text).translate(_BLANK)


def _tw(text, fonts) -> float:
    return sum(_font_for(fonts, c).getlength(c) for c in _vis(text))


def _dt(d, xy, text, fonts, fill, stroke=0, stroke_fill=None):
    """Draw text on a baseline, picking a font per character (handles fancy unicode)."""
    x, y = xy
    for c in _vis(text):
        f = _font_for(fonts, c)
        d.text((x, y), c, font=f, fill=fill, anchor="ls", stroke_width=stroke, stroke_fill=stroke_fill)
        x += f.getlength(c)


def _shear(layer, k=0.22):
    w, h = layer.size
    return layer.transform((w + int(k * h), h), Image.AFFINE, (1, k, -k * h, 0, 1, 0), Image.BICUBIC)


def _title_layer(text, size, fill=(255, 255, 255, 255), glow=(255, 40, 30), slant=0.22):
    fonts = _fonts(size)
    pad = 30
    w, h = int(_tw(text, fonts)) + pad * 2, int(size * 1.6)
    lay = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    _dt(ImageDraw.Draw(lay), (pad, int(size * 1.15)), text, fonts, fill)
    lay = _shear(lay, slant)
    alpha = lay.split()[3].filter(ImageFilter.GaussianBlur(max(2, size // 6)))
    gl = Image.new("RGBA", lay.size, glow + (0,))
    gl.putalpha(alpha)
    out = Image.new("RGBA", lay.size, (0, 0, 0, 0))
    out.alpha_composite(gl)
    out.alpha_composite(gl)
    out.alpha_composite(lay)
    return out


def _bg(W, H):
    rnd = random.Random(7)
    base = Image.new("RGB", (W, H), (7, 0, 3))
    glow = Image.new("RGB", (W, H), (0, 0, 0))
    gd = ImageDraw.Draw(glow)
    gd.ellipse((W * 0.08, H * 0.1, W * 0.92, H * 0.9), fill=(125, 8, 14))
    gd.ellipse((W * 0.3, H * 0.28, W * 0.7, H * 0.72), fill=(95, 10, 10))
    glow = glow.filter(ImageFilter.GaussianBlur(W // 7))
    img = ImageChops.add(base, glow).convert("RGBA")
    lay = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ld = ImageDraw.Draw(lay)
    for _ in range(110):
        x, y = rnd.randint(-100, W), rnd.randint(0, H + 100)
        n = rnd.randint(70, 280)
        ld.line((x, y, x + n * 0.5, y - n * 0.87), fill=(255, rnd.randint(20, 80), 20, rnd.randint(70, 210)), width=rnd.choice([1, 2, 2, 3]))
    img.alpha_composite(lay.filter(ImageFilter.GaussianBlur(5)))
    img.alpha_composite(lay)
    vig = Image.new("L", (W, H), 0)
    ImageDraw.Draw(vig).ellipse((-W * 0.25, -H * 0.25, W * 1.25, H * 1.25), fill=255)
    vig = vig.filter(ImageFilter.GaussianBlur(W // 6))
    dark = Image.new("RGBA", (W, H), (0, 0, 0, 255))
    img = Image.composite(img, dark, vig)
    return img


def _rarity_color(r):
    r = (r or "").lower()
    for key, col in (
        ("artifact", (255, 70, 70)),
        ("mythic+", (255, 140, 20)),
        ("mythic", (255, 205, 40)),
        ("epic", (190, 70, 255)),
        ("rare", (60, 150, 255)),
        ("uncommon", (70, 220, 100)),
        ("common", (235, 235, 235)),
    ):
        if key in r:
            return col
    return (200, 200, 200)


def _open(data):
    try:
        return Image.open(io.BytesIO(data)).convert("RGBA") if data else None
    except Exception:
        return None


def safe_name(name, fallback="Player"):
    """Name for images: drops characters the font cannot draw (no boxes); falls back to a plain label."""
    t = _vis(clean(name))
    fonts = _fonts(40)
    out = "".join(c for c in t if c.isspace() or any(_has(f, c) for f in fonts))
    out = re.sub(r"\s+", " ", out).strip()
    return out if sum(ch.isalnum() for ch in out) >= 2 else fallback


def _fit(text, max_w, size, min_size=14):
    """Largest font that fits max_w; adds an ellipsis if even min_size is too wide."""
    text = str(text or "")
    sz = size
    while sz > min_size and _tw(text, _fonts(sz)) > max_w:
        sz -= 2
    fonts = _fonts(sz)
    if text and _tw(text, fonts) > max_w:
        while text and _tw(text + "…", fonts) > max_w:
            text = text[:-1]
        text = text.rstrip() + "…"
    return text, fonts


def _round(im, size, radius=18):
    im = ImageOps.fit(im, (size, size), Image.LANCZOS)
    m = Image.new("L", (size, size), 0)
    ImageDraw.Draw(m).rounded_rectangle((0, 0, size - 1, size - 1), radius, fill=255)
    im.putalpha(ImageChops.multiply(im.split()[3], m))
    return im


def _slot(img, x, y, s, icon, color, label=""):
    pad = 40
    lay = Image.new("RGBA", (s + 2 * pad, s + 2 * pad), (0, 0, 0, 0))
    ImageDraw.Draw(lay).rounded_rectangle((pad, pad, pad + s, pad + s), 14, outline=color + (255,), width=8)
    bl = lay.filter(ImageFilter.GaussianBlur(10))
    img.paste(bl, (x - pad, y - pad), bl)
    d = ImageDraw.Draw(img)
    d.rounded_rectangle((x, y, x + s, y + s), 14, fill=(16, 6, 12, 255), outline=color + (255,), width=3)
    ramp = Image.linear_gradient("L").resize((s - 8, s - 8)).point(lambda v: int(v * 0.5))
    tint = Image.new("RGBA", (s - 8, s - 8), color + (255,))
    tint.putalpha(ramp)
    img.paste(tint, (x + 4, y + 4), tint)
    band = 44 if label else 0
    if icon is not None:
        ic = ImageOps.contain(icon, (s - 36, s - 36 - band), Image.LANCZOS)
        img.paste(ic, (x + (s - ic.width) // 2, y + 10 + (s - 20 - band - ic.height) // 2), ic)
    else:
        txt, f = _fit("NO IMAGE" if label else "EMPTY", s - 40, 22, 12)
        _dt(d, (x + (s - _tw(txt, f)) / 2, y + (s - band) // 2 + 8), txt, f, (150, 80, 80, 255))
    if label:
        bar = Image.new("RGBA", (s - 8, band), (0, 0, 0, 190))
        img.paste(bar, (x + 4, y + s - band - 4), bar)
        d.rectangle((x + 4, y + s - band - 5, x + s - 4, y + s - band - 3), fill=color + (255,))
        txt, f = _fit(label, s - 24, 22, 16)
        _dt(d, (x + (s - _tw(txt, f)) / 2, y + s - 17), txt, f, (255, 255, 255, 255))


def _jpeg(img, q=92):
    buf = io.BytesIO()
    img.convert("RGB").save(buf, "JPEG", quality=q)
    return buf.getvalue()


def _watermark(img, x_right, y, size=88):
    wm = _title_layer(WATERMARK, size, glow=(255, 30, 30))
    img.paste(wm, (x_right - wm.width, y), wm)


def _chip(img, x, y, label, value, h=56):
    """Small stat box: tiny label on top, value below. Returns the next free x."""
    d = ImageDraw.Draw(img)
    fl, fv = _fonts(16), _fonts(28)
    value = str(value)
    w = int(max(_tw(label, fl), _tw(value, fv))) + 34
    box = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    ImageDraw.Draw(box).rounded_rectangle((0, 0, w - 1, h - 1), 12, fill=(0, 0, 0, 170), outline=(235, 35, 35, 255), width=2)
    img.paste(box, (x, y), box)
    _dt(d, (x + 17, y + 22), label, fl, (255, 150, 150, 255))
    _dt(d, (x + 17, y + 49), value, fv, (255, 255, 255, 255))
    return x + w + 14


def render_loadout(js, icons, rarity, names=None):
    """3x3 ring of equipped items around the avatar, item names under each icon."""
    names = names or {}
    W, H = 1080, 1190
    img = _bg(W, H)
    b, p = js.get("basic_info") or {}, js.get("profile_info") or {}
    t = _title_layer("PLAYER LOADOUT", 64)
    img.paste(t, (50, 28), t)
    _watermark(img, W - 40, 22, 68)

    S, G = 250, 28
    x0, y0 = (W - 3 * S - 2 * G) // 2, 175
    cell = lambda r, c: (x0 + c * (S + G), y0 + r * (S + G))  # noqa: E731
    order = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)]
    ids = [i for i in (p.get("equipped_skills") or []) + (b.get("weapon_skin_shows") or []) if i][:8]

    cx, cy = cell(1, 1)
    lay = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ld = ImageDraw.Draw(lay)
    for r, c in order:
        ox, oy = cell(r, c)
        ld.line((cx + S // 2, cy + S // 2, ox + S // 2, oy + S // 2), fill=(255, 50, 40, 210), width=4)
    img.alpha_composite(lay.filter(ImageFilter.GaussianBlur(6)))
    img.alpha_composite(lay)

    for n, (r, c) in enumerate(order):
        x, y = cell(r, c)
        i = ids[n] if n < len(ids) else None
        col = _rarity_color(rarity.get(str(i), "")) if i else (120, 60, 60)
        label = (names.get(str(i)) or str(i)) if i else ""
        _slot(img, x, y, S, _open(icons.get(str(i))) if i else None, col, label)
    av = p.get("avatar_id") or b.get("head_pic")
    center = _open(icons.get(str(p.get("avatar_id")))) or _open(icons.get(str(b.get("head_pic"))))
    _slot(img, cx, cy, S, center, (255, 205, 40), (names.get(str(av)) or "AVATAR") if av else "AVATAR")

    # footer panel
    fy, fh = 1018, 140
    panel = Image.new("RGBA", (W - 100, fh), (0, 0, 0, 0))
    ImageDraw.Draw(panel).rounded_rectangle((0, 0, W - 101, fh - 1), 18, fill=(10, 2, 6, 205), outline=(235, 35, 35, 255), width=3)
    img.paste(panel, (50, fy), panel)
    d = ImageDraw.Draw(img)
    name = safe_name(b.get("nickname"))
    txt, f = _fit(name, 560, 46, 24)
    _dt(d, (80, fy + 62), txt, f, (255, 255, 255, 255), stroke=2, stroke_fill=(40, 0, 0, 255))
    _dt(d, (80, fy + 108), f"UID {b.get('account_id', '')}", _fonts(28), (255, 150, 150, 255))
    chips = [("LEVEL", b.get("level", "-")), ("BR PTS", b.get("ranking_points", "-"))]
    widths = []
    for lab, val in chips:
        widths.append(int(max(_tw(lab, _fonts(16)), _tw(str(val), _fonts(28)))) + 34 + 14)
    x = W - 80 - sum(widths) + 14
    for lab, val in chips:
        x = _chip(img, x, fy + 42, lab, val)
    return _jpeg(img)


def render_banner(js, icons, names=None):
    """Full profile banner (never cropped) + an info panel underneath."""
    b = js.get("basic_info") or {}
    W, PH = 1000, 210
    ban = _open(icons.get(str(b.get("banner_id"))))
    if ban is not None:
        HB = int(max(190, min(440, W * ban.height / ban.width)))
        top = ImageOps.fit(ban, (W, HB), Image.LANCZOS).filter(ImageFilter.GaussianBlur(18))
        top.alpha_composite(Image.new("RGBA", (W, HB), (0, 0, 0, 110)))
        fg = ImageOps.contain(ban, (W, HB), Image.LANCZOS)
        top.paste(fg, ((W - fg.width) // 2, (HB - fg.height) // 2), fg)
    else:
        HB = 230
        grad = Image.linear_gradient("L").resize((W, HB))
        top = Image.composite(Image.new("RGBA", (W, HB), (235, 70, 140, 255)), Image.new("RGBA", (W, HB), (240, 150, 190, 255)), grad)
    img = Image.new("RGBA", (W, HB + PH), (0, 0, 0, 255))
    img.paste(top, (0, 0))
    img.paste(_bg(W, PH), (0, HB))
    d = ImageDraw.Draw(img)
    d.rectangle((0, HB - 2, W, HB + 3), fill=(235, 35, 35, 255))

    A = 150
    ax, ay = 30, HB + 30
    av = _open(icons.get(str(b.get("head_pic"))))
    d.rounded_rectangle((ax - 4, ay - 4, ax + A + 3, ay + A + 3), 20, fill=(16, 6, 12, 255), outline=(255, 205, 40, 255), width=4)
    if av is not None:
        r = _round(av, A, 16)
        img.paste(r, (ax, ay), r)

    tx = ax + A + 32
    name = safe_name(b.get("nickname"))
    txt, f = _fit(name, W - tx - 30, 58, 26)
    _dt(d, (tx, HB + 82), txt, f, (255, 255, 255, 255), stroke=3, stroke_fill=(40, 0, 0, 255))
    _dt(d, (tx, HB + 118), f"UID {b.get('account_id', '')}", _fonts(26), (255, 150, 150, 255))
    x = tx
    for lab, val in (("LEVEL", b.get("level", "-")), ("LIKES", indian(b.get("liked", 0))), ("BR PTS", b.get("ranking_points", "-"))):
        x = _chip(img, x, HB + 136, lab, val)
    _watermark(img, W - 24, HB + 112, 54)
    return _jpeg(img)


def render_item_card(icon_bytes, it):
    W = H = 1080
    img = _bg(W, H)
    t = _title_layer("ITEM", 64)
    img.paste(t, (50, 30), t)
    S = 560
    _slot(img, (W - S) // 2, 150, S, _open(icon_bytes), _rarity_color(it.get("rarity", "")))
    d = ImageDraw.Draw(img)
    name = it.get("name") or f"ID {it.get('id', '')}"
    size = 60
    while size > 28 and _tw(name, _fonts(size)) > W - 120:
        size -= 4
    f = _fonts(size)
    _dt(d, ((W - _tw(name, f)) / 2, 850), name, f, (255, 255, 255, 255), stroke=2, stroke_fill=(40, 0, 0, 255))
    idt = f"ID {it.get('id', '')}"
    f2 = _fonts(34)
    _dt(d, ((W - _tw(idt, f2)) / 2, 905), idt, f2, (255, 150, 150, 255))
    _watermark(img, W - 40, H - 150)
    return _jpeg(img)


_WELCOME = {}


def render_welcome():
    if "img" in _WELCOME:
        return _WELCOME["img"]
    W, H = 1080, 560
    img = _bg(W, H)
    t = _title_layer("PLAYER INFO BOT", 96)
    img.paste(t, ((W - t.width) // 2, 130), t)
    d = ImageDraw.Draw(img)
    sub = "Free Fire  •  Player & Item Lookup"
    f = _fonts(36)
    _dt(d, ((W - _tw(sub, f)) / 2, 370), sub, f, (255, 170, 170, 255))
    _watermark(img, W - 40, H - 140, 72)
    _WELCOME["img"] = _jpeg(img)
    return _WELCOME["img"]


async def build_cards(js, nm):
    """Returns [banner, loadout] jpeg bytes (any that fail are skipped)."""
    if not PIL_OK:
        return []
    b, p = js.get("basic_info") or {}, js.get("profile_info") or {}
    ids = [i for i in (p.get("equipped_skills") or []) + (b.get("weapon_skin_shows") or []) if i][:8]
    extra = [p.get("avatar_id"), b.get("head_pic"), b.get("banner_id")]
    want = []
    for i in ids + extra:
        if i and i not in want:
            want.append(i)
    got = await asyncio.gather(*[fetch_icon(i) for i in want], return_exceptions=True)
    icons = {str(i): g for i, g in zip(want, got) if isinstance(g, (bytes, bytearray))}
    rarity = {}
    for i in ids:
        hit = ITEM_CACHE.get(str(i))
        if hit and hit[1]:
            rarity[str(i)] = hit[1].get("rarity", "")
    out = []
    for fn, args in ((render_banner, (js, icons, nm)), (render_loadout, (js, icons, rarity, nm))):
        try:
            out.append(await asyncio.to_thread(fn, *args))
        except Exception as e:
            log.warning("card render failed: %r", e)
    return out


# ───────────────────────── player ─────────────────────────
async def fetch_player(uid, force=False):
    hit = PLAYER_CACHE.get(uid)
    if hit and not force and time.time() - hit[0] < CACHE_TTL:
        return hit[1]
    last = None
    for attempt in range(3):
        try:
            r = await http().get(INFO_API, params={"uid": uid})
            r.raise_for_status()
            js = r.json()
            if isinstance(js, dict) and js.get("basic_info"):
                PLAYER_CACHE[uid] = (time.time(), js)
                trim(PLAYER_CACHE, 300)
                return js
            last = ValueError(f"basic_info missing: {str(js)[:120]}")
        except httpx.HTTPStatusError as e:
            last = e
            if e.response.status_code < 500 or attempt >= 1:  # wrong UID answers the same every time
                break
        except Exception as e:
            last = e
        log.warning("player fetch attempt %s failed: %r", attempt + 1, last)
        await asyncio.sleep(1)
    raise last


def collect_ids(js):
    b = js.get("basic_info") or {}
    p = js.get("profile_info") or {}
    pet = js.get("pet_info") or {}
    ids = [
        b.get("badge_id"), b.get("banner_id"), b.get("head_pic"), b.get("title"),
        p.get("avatar_id"), pet.get("pet_id"), pet.get("skin_id"), pet.get("selected_skill_id"),
    ]
    ids += b.get("weapon_skin_shows") or []
    ids += p.get("equipped_skills") or []
    out = []
    for i in ids:
        if i and i not in out:
            out.append(i)
    return out[:18]


def _jl(items):
    return [cp(json.dumps(x, ensure_ascii=False)) for x in items or []]


def build_player(js, nm):
    b = js.get("basic_info") or {}
    p = js.get("profile_info") or {}
    cl = js.get("clan_basic_info") or {}
    cap = js.get("captain_basic_info") or {}
    pet = js.get("pet_info") or {}
    so = js.get("social_info") or {}
    cr = js.get("credit_score_info") or {}
    pr = b.get("account_prefers") or {}
    n = lambda i: nm.get(str(i), "")  # noqa: E731

    nick = b.get("nickname", "")
    basic = [R("Name", nick)]
    if clean(nick) != nick:
        basic.append(R("Name (clean)", clean(nick)))
    basic += [
        R("UID", b.get("account_id")),
        R("Account Type", b.get("account_type")),
        R("Level", b.get("level")),
        R("EXP", b.get("exp"), fmt=indian),
        R("Likes", b.get("liked"), fmt=indian),
        R("Badges", b.get("badge_cnt")),
        R("Badge ID", b.get("badge_id"), n(b.get("badge_id"))),
        R("Banner ID", b.get("banner_id"), n(b.get("banner_id"))),
        R("Head Pic", b.get("head_pic"), n(b.get("head_pic"))),
        R("Title", b.get("title"), n(b.get("title"))),
        R("Prime Level", (b.get("prime_info") or {}).get("prime_level")),
        R("Booyah Pass", "Premium" if b.get("has_elite_pass") else "Normal"),
        R("Created", b.get("create_at"), fmt=ts),
        R("Last Login", b.get("last_login_at"), fmt=ts),
        R("Version", b.get("release_version")),
    ]

    rank = [
        R("BR Rank", b.get("rank"), br_rank(b.get("rank"))),
        R("BR Points", b.get("ranking_points")),
        R("BR Max Rank", b.get("max_rank"), br_rank(b.get("max_rank"))),
        R("CS Rank", b.get("cs_rank")),
        R("CS Points", b.get("cs_ranking_points")),
        R("CS Max Rank", b.get("cs_max_rank")),
        R("Hippo Rank", b.get("hippo_rank")),
        R("Hippo Points", b.get("hippo_ranking_points")),
        R("Season", b.get("season_id")),
        R("Peak Rank Pos", b.get("peak_rank_pos")),
        R("Leaderboard Pos", js.get("ranking_leaderboard_pos")),
        E("Show Rank", b.get("show_rank")),
        E("Show BR Rank", b.get("show_br_rank")),
        E("Show CS Rank", b.get("show_cs_rank")),
        L("CS Rank Entries", _jl(b.get("cs_rank_entries"))),
    ]

    gname = cl.get("clan_name", "")
    guild = [R("Name", gname)]
    if clean(gname) != gname:
        guild.append(R("Name (clean)", clean(gname)))
    guild += [
        R("Guild ID", cl.get("clan_id")),
        R("Level", cl.get("clan_level")),
        R("Members", f"{cl.get('current_members', 0)}/{cl.get('max_members', 0)}"),
        R("Leader ID", cl.get("captain_id")),
        R("Leader Name", cap.get("nickname")),
        R("Leader Level", cap.get("level")),
        R("Leader EXP", cap.get("exp"), fmt=indian),
        R("Leader Likes", cap.get("liked"), fmt=indian),
        R("Leader BR Rank", cap.get("rank"), br_rank(cap.get("rank"))),
        R("Leader BR Points", cap.get("ranking_points")),
        R("Leader Last Login", cap.get("last_login_at"), fmt=ts),
    ]

    petrows = [
        R("Name", pet.get("pet_name")),
        R("Pet ID", pet.get("pet_id"), n(pet.get("pet_id"))),
        R("Level", pet.get("level")),
        R("EXP", pet.get("exp")),
        B("Selected", pet.get("is_selected")),
        R("Skin ID", pet.get("skin_id"), n(pet.get("skin_id"))),
        R("Skill ID", pet.get("selected_skill_id"), n(pet.get("selected_skill_id"))),
    ]

    bio = so.get("social_highlight", "")
    privacy = so.get("privacy", "")
    social = [R("Gender", enum_txt(so.get("gender", ""), "GENDER_")), R("Language", so.get("language")), R("Bio", bio)]
    if clean(bio) != bio:
        social.append(R("Bio (clean)", clean(bio)))
    social += [
        R("Privacy", enum_txt(privacy, "PRIVACY_")),
        R("Region", ((so.get("region_stats") or [{}])[0] or {}).get("region_code") or b.get("region")),
    ]

    load = [
        L("Equipped Items", [id_line(i, nm) for i in p.get("equipped_skills") or []]),
        L("Skill Slots", [f"slot {s.get('slot_index')} → {cp(s.get('skill_id'))}" for s in p.get("skill_slots") or []]),
        R("PvE Weapon", p.get("pve_primary_weapon")),
        R("Avatar ID", p.get("avatar_id"), n(p.get("avatar_id"))),
        L("Cosmetic Items", [id_line(i, nm) for i in p.get("cosmetic_items") or []]),
        L("Weapon Skins", [id_line(i, nm) for i in b.get("weapon_skin_shows") or []]),
        R("Skin Unlock Time", p.get("skin_unlock_time")),
    ]

    acc = [
        R("Honor Score", cr.get("score")),
        R("Honor Status", cr.get("status")),
        R("Honor Start", cr.get("start"), fmt=ts),
        R("Honor End", cr.get("end"), fmt=ts),
        R("Honor Reason", cr.get("reason")),
        R("Diamond Cost", (js.get("diamond_cost_res") or {}).get("diamond_cost")),
        B("Hide Clan Info", pr.get("hide_clan_info")),
        B("Hide Weapon Skins", pr.get("hide_weapon_skins")),
        E("Show Booyah Pass", pr.get("show_elite_pass")),
        E("Show Title", pr.get("show_title")),
    ]

    return [
        f"<b>{fx('Player Profile Info')}</b>",
        section("Basic", basic),
        section("Account", acc),
        section("Social", social),
        section("Pet", petrows),
        section("Rank", rank),
        section("Loadout", load),
        section("Guild", guild),
        f"{esc(js.get('Time_Spne', ''))} · {esc(WATERMARK)}",
    ]


# ───────────────────────── handlers ─────────────────────────
DEFAULT_WELCOME = (
    f"<b>{fx('Free Fire Player Info')}</b>\n"
    "Welcome, {mention}\n\n"
    "Full profile, loadout and item details from just a UID.\n\n"
    f"<b>{fx('What you get')}</b>\n"
    "├ Profile banner and loadout card\n"
    "├ Rank, guild, pet, Honor Score and Booyah Pass\n"
    "└ Item names with pictures\n\n"
    f"<b>{fx('Try it')}</b>\n"
    "├ /info &lt;uid&gt;\n"
    "├ /item &lt;id or name&gt;\n"
    "└ /track &lt;uid&gt; (live alerts, private chat)\n\n"
    f"<b>{fx('Your plan')}</b>\n"
    "├ Track up to {limit} players\n"
    "└ {searches} searches per day\n\n"
    "<i>All commands: /help</i>"
)


def welcome_caption(user=None, bot_name=""):
    uid = getattr(user, "id", 0) or 0
    first = (getattr(user, "first_name", "") or getattr(user, "username", "") or "there").strip()
    full = " ".join(x for x in (getattr(user, "first_name", "") or "", getattr(user, "last_name", "") or "") if x).strip() or first
    sd = int(CFG.get("search_daily", 0))
    fields = {"{name}": esc(full), "{first}": esc(first), "{id}": str(uid),
              "{mention}": f'<a href="tg://user?id={uid}">{esc(full)}</a>' if uid else esc(full),
              "{limit}": lim_txt(uid) if uid else str(CFG["limit_default"]),
              "{searches}": str(sd) if sd > 0 and not is_owner(uid) else "Unlimited", "{bot}": esc(bot_name)}
    t = CFG.get("welcome") or DEFAULT_WELCOME
    for k, v in fields.items():
        t = t.replace(k, v)
    return t


def help_text():
    return (
        f"<b>{fx('Command Guide')}</b>\n"
        "Send a command followed by a player UID.\n\n"
        f"<b>{fx('Player')}</b>\n"
        "/info &lt;uid&gt; — full profile with banner &amp; loadout card\n"
        "/level &lt;uid&gt; — level, EXP, likes &amp; prime level\n"
        "/bio &lt;uid&gt; — signature / bio text\n"
        "/outfit &lt;uid&gt; — equipped items &amp; weapon skins\n"
        "/rank &lt;uid&gt; — BR &amp; CS rank with points\n"
        "/login &lt;uid&gt; — account created &amp; last login\n\n"
        f"<b>{fx('Guild')}</b>\n"
        "/clan &lt;uid&gt; — guild name, level &amp; members\n"
        "/leader &lt;uid&gt; — guild leader's details\n\n"
        f"<b>{fx('Pet')}</b>\n"
        "/pet &lt;uid&gt; — pet name, level, skin &amp; skill\n\n"
        f"<b>{fx('Items')}</b>\n"
        "/item &lt;id&gt; — item details with picture\n"
        "/item &lt;name&gt; — search items by name\n\n"
        f"<b>{fx('Live tracking')}</b> (private chat only)\n"
        "/track &lt;uid&gt; — instant alert on profile changes (you choose which ones)\n"
        "/tracklist — everyone you track, with details &amp; alert settings\n"
        "/untrack &lt;uid|all&gt; — stop tracking\n"
        "/quiet &lt;from&gt; &lt;to&gt; — mute tracking alerts at night (IST hours)\n"
        "/history — your last searched UIDs\n"
        "/plan — your limits\n\n"
        f"<b>{fx('Tips')}</b>\n"
        "• Send /info followed by the player UID\n"
        "• Without a slash also works: info &lt;uid&gt;\n"
        "• Tap any value in the results to copy it\n"
        "• Works in groups: /info@botusername &lt;uid&gt;"
    )


def duplicate(update) -> bool:
    """True if this exact Telegram update was already handled (re-delivery guard)."""
    now = time.time()
    if len(SEEN) > 500:
        for k in [k for k, t in SEEN.items() if now - t > 300]:
            SEEN.pop(k, None)
    if update.update_id in SEEN:
        return True
    SEEN[update.update_id] = now
    return False


def limited(user_id) -> bool:
    now = time.time()
    if now - LAST_USE.get(user_id, 0) < COOLDOWN:
        return True
    LAST_USE[user_id] = now
    trim(LAST_USE, 3000)
    return False


async def action(msg, act):
    try:
        await msg.chat.send_action(act)
    except Exception:
        pass


async def send_parts(msg, parts, kb=None):
    for i, part in enumerate(parts):
        last = i == len(parts) - 1
        await rt(msg, part, add=last, parse_mode=ParseMode.HTML, reply_markup=kb if last else None)


async def send_photo(msg, photo, text) -> bool:
    """Send photo (+ text as caption, or as a follow-up if too long).
    Returns True when the photo is out or MAY be out (timeout) so the caller must never
    send the same text again; False only when Telegram clearly rejected the photo."""
    cap = text if len(text) <= 980 else None
    try:
        if cap:
            await rp(msg, photo, caption=cap, parse_mode=ParseMode.HTML, **TO)
        else:
            await rp(msg, photo, **TO)
    except TimedOut:
        log.warning("photo upload timed out - not resending")
        return True
    except Exception as e:
        log.warning("photo send failed: %r", e)
        return False
    if cap is None:
        try:
            await send_parts(msg, pack([text]))
        except Exception as e:
            log.warning("text after photo failed: %r", e)
    return True


async def send_cards(msg, cards):
    """Banner + loadout as one album (single card -> normal photo). Never raises."""
    if not cards:
        return
    try:
        if len(cards) == 1:
            await rp(msg, cards[0], **TO)
        else:
            await msg.reply_media_group(media=[InputMediaPhoto(c) for c in cards], **TO)
        return
    except TimedOut:
        log.warning("album upload timed out - not resending")
        return
    except Exception as e:
        log.warning("album send failed: %r", e)
    for c in cards:  # album rejected as a whole -> nothing was delivered yet
        try:
            await rp(msg, c, **TO)
        except Exception as e:
            log.warning("card send failed: %r", e)


async def build_cards_safe(js, nm):
    try:
        return await asyncio.wait_for(build_cards(js, nm), timeout=40)
    except Exception as e:
        log.warning("cards failed: %r", e)
        return []


async def handle_info(msg, uid, force=False, by=None):
    if not await search_ok(msg, by, uid):
        return
    await action(msg, ChatAction.TYPING)
    try:
        js = await fetch_player(uid, force)
        search_done(by, uid)
    except Exception as e:
        log.warning("player fetch failed %s: %r", uid, e)
        await rt(msg, fail_text(e))
        return
    nm = await resolve_names(collect_ids(js))
    # images are rendered in the background while the details go out first
    cards_task = asyncio.create_task(build_cards_safe(js, nm)) if PIL_OK else None
    row = [InlineKeyboardButton("Refresh", callback_data=f"r:{uid}")]
    lead_id = (js.get("clan_basic_info") or {}).get("captain_id")
    if lead_id and str(lead_id) != str(uid):
        row.append(InlineKeyboardButton("Leader", callback_data=f"c:{lead_id}"))
    try:
        await send_parts(msg, pack(build_player(js, nm)), InlineKeyboardMarkup([row]))
    except Exception as e:
        log.warning("details send failed: %r", e)
        if cards_task:
            cards_task.cancel()
        try:
            await rt(msg, "Couldn't send the info. Please try again.")
        except Exception:
            pass
        return
    if cards_task:
        await action(msg, ChatAction.UPLOAD_PHOTO)
        await send_cards(msg, await cards_task)


def item_text(it):
    rows = []
    for lab, key in (("Name", "name"), ("Item ID", "id"), ("Type", "type"), ("Rarity", "rarity"), ("Icon Name", "icon"), ("Description", "desc")):
        if it.get(key):
            rows.append(R(lab, it[key]))
    return section("Item Info", rows)


async def handle_item(msg, arg):
    await action(msg, ChatAction.TYPING)
    arg = arg.strip()
    is_id = arg.isdigit()
    it, results = None, []
    try:
        if is_id:
            it = await get_item(arg)
        else:
            results = await search_items(arg)
            if len(results) == 1:
                it = results[0]
    except Exception as e:
        log.warning("item search failed %s: %r", arg, e)
        if not is_id:
            await rt(msg, "Item search is unavailable right now. Please try again in a moment.")
            return
    if not is_id:
        if not results:
            await rt(msg, "No items found.")
            return
        if len(results) > 1:
            lines = [f"{cp(x['id'])} → {esc(x['name'])}" for x in results[:15]]
            await rt(msg, 
                f"<b>{len(results)} {fx('results')}</b>\n" + "\n".join(lines) + "\n\n<code>/item &lt;id&gt;</code>",
                parse_mode=ParseMode.HTML,
            )
            return
    iid = it["id"] if it else arg
    icon = await fetch_icon(iid)
    if not it and not icon:
        await rt(msg, "Item not found.")
        return
    it = it or {"id": iid, "name": "", "desc": "", "icon": "", "type": "", "rarity": ""}
    text = item_text(it)
    photo = icon
    if icon and PIL_OK:
        await action(msg, ChatAction.UPLOAD_PHOTO)
        try:
            photo = await asyncio.to_thread(render_item_card, icon, it)
        except Exception as e:
            log.warning("item card failed: %r", e)
    if photo and await send_photo(msg, photo, text):
        return
    await send_parts(msg, pack([text]))


QUICK = ("level", "bio", "outfit", "rank", "clan", "leader", "pet", "login")
QUICK_RE = re.compile(r"^\s*[/!.#]?\s*(?P<c>" + "|".join(QUICK) + r")(?:@\w+)?\s*[:=\-]?\s*(?P<u>\d{5,13})\s*$", re.I)


def quick_text(js, nm, kind):
    b = js.get("basic_info") or {}
    p = js.get("profile_info") or {}
    cl = js.get("clan_basic_info") or {}
    ld = js.get("captain_basic_info") or {}
    pet = js.get("pet_info") or {}
    so = js.get("social_info") or {}
    n = lambda i: nm.get(str(i), "")  # noqa: E731
    head = [R("Name", b.get("nickname")), R("UID", b.get("account_id"))]

    if kind == "level":
        title = "Level"
        rows = [R("Level", b.get("level")), R("EXP", b.get("exp"), fmt=indian),
                R("Likes", b.get("liked"), fmt=indian), R("Prime Level", (b.get("prime_info") or {}).get("prime_level"))]
    elif kind == "bio":
        title = "Bio"
        bio = so.get("social_highlight", "")
        rows = [R("Bio", bio)]
        if clean(bio) != bio:
            rows.append(R("Bio (clean)", clean(bio)))
    elif kind == "outfit":
        title = "Outfit"
        rows = [
            L("Equipped Items", [id_line(i, nm) for i in p.get("equipped_skills") or []]),
            R("Avatar ID", p.get("avatar_id"), n(p.get("avatar_id"))),
            R("Banner ID", b.get("banner_id"), n(b.get("banner_id"))),
            R("Head Pic", b.get("head_pic"), n(b.get("head_pic"))),
            R("Title", b.get("title"), n(b.get("title"))),
            L("Cosmetic Items", [id_line(i, nm) for i in p.get("cosmetic_items") or []]),
            L("Weapon Skins", [id_line(i, nm) for i in b.get("weapon_skin_shows") or []]),
        ]
    elif kind == "rank":
        title = "Rank"
        rows = [
            R("BR Rank", b.get("rank"), br_rank(b.get("rank"))),
            R("BR Points", b.get("ranking_points")),
            R("BR Max Rank", b.get("max_rank"), br_rank(b.get("max_rank"))),
            R("CS Rank", b.get("cs_rank")), R("CS Points", b.get("cs_ranking_points")),
            R("CS Max Rank", b.get("cs_max_rank")),
        ]
    elif kind == "pet":
        title = "Pet"
        rows = [
            R("Pet Name", pet.get("pet_name")), R("Pet Level", pet.get("level")), R("Pet EXP", pet.get("exp")),
            R("Skin ID", pet.get("skin_id"), n(pet.get("skin_id"))),
            R("Skill ID", pet.get("selected_skill_id"), n(pet.get("selected_skill_id"))),
        ]
    elif kind == "login":
        title = "Activity"
        rows = [R("Created", b.get("create_at"), fmt=ts), R("Last Login", b.get("last_login_at"), fmt=ts),
                R("Version", b.get("release_version"))]
    elif kind == "leader":
        title = "Leader"
        head = []
        rows = [
            R("Leader ID", cl.get("captain_id")), R("Leader Name", ld.get("nickname")),
            R("Leader Level", ld.get("level")), R("Leader EXP", ld.get("exp"), fmt=indian),
            R("Leader Likes", ld.get("liked"), fmt=indian),
            R("Leader BR Rank", ld.get("rank"), br_rank(ld.get("rank"))),
            R("Leader BR Points", ld.get("ranking_points")),
            R("Leader Last Login", ld.get("last_login_at"), fmt=ts),
        ]
    else:  # clan
        title = "Guild"
        head = []
        rows = [
            R("Name", cl.get("clan_name")), R("Guild ID", cl.get("clan_id")),
            R("Level", cl.get("clan_level")),
            R("Members", f"{cl.get('current_members', 0)}/{cl.get('max_members', 0)}"),
            R("Leader ID", cl.get("captain_id")), R("Leader Name", ld.get("nickname")),
        ]
    return [section(title, head + rows)]


async def handle_quick(msg, kind, uid, by=None):
    if not await search_ok(msg, by, uid):
        return
    await action(msg, ChatAction.TYPING)
    try:
        js = await fetch_player(uid)
        search_done(by, uid)
    except Exception as e:
        log.warning("quick fetch failed %s: %r", uid, e)
        await rt(msg, fail_text(e))
        return
    nm = await resolve_names(collect_ids(js)) if kind in ("outfit", "pet") else {}
    await send_parts(msg, pack(quick_text(js, nm, kind)))


INFO_RE = re.compile(r"^\s*[/!.#]?\s*(?:info|get|uid)(?:@\w+)?\s*[:=\-]?\s*(\d{5,13})\s*$", re.I)
ITEM_RE = re.compile(r"^\s*(?P<p>[/!.#])?\s*item(?:@\w+)?\s*[:=\-]?\s*(?P<a>.+?)\s*$", re.I)
BARE_RE = re.compile(r"^\s*[/!.#]\s*(?P<c>info|get|uid|item|level|bio|outfit|rank|clan|leader|pet|login)(?:@\w+)?\s*$", re.I)


async def router(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not msg or not msg.text or not update.effective_user:
        return
    if duplicate(update):
        return
    text, uid = msg.text, update.effective_user.id
    bn_ok = lambda m: not (m.group("b") and ctx.bot.username and m.group("b").lower() != ctx.bot.username.lower())

    m = OWN_RE.match(text)
    if m:
        if bn_ok(m) and is_owner(uid):
            note_user(update.effective_user, str(getattr(msg.chat, "type", "")))
            await owner_cmd(update, ctx, msg, m.group("c").lower(), m.group("a") or "")
        return
    m = USER_RE.match(text)
    if m:
        if bn_ok(m) and not await gate(update, ctx.bot, msg):
            await user_cmd(update, ctx, msg, m.group("c").lower(), m.group("a"))
        return
    m = TRACK_RE.match(text)
    if m:
        if bn_ok(m) and not await gate(update, ctx.bot, msg):
            await handle_track(update, ctx, msg, m.group("c").lower(), m.group("a"))
        return
    m = INFO_RE.match(text)
    if m:
        if await gate(update, ctx.bot, msg):
            return
        if limited(uid):
            await rt(msg, "Slow down a little.")
            return
        await handle_info(msg, m.group(1), by=uid)
        return
    m = QUICK_RE.match(text)
    if m:
        if await gate(update, ctx.bot, msg):
            return
        if limited(uid):
            await rt(msg, "Slow down a little.")
            return
        await handle_quick(msg, m.group("c").lower(), m.group("u"), by=uid)
        return
    m = ITEM_RE.match(text)
    if m and (m.group("a").isdigit() or m.group("p")):
        if await gate(update, ctx.bot, msg):
            return
        if limited(uid):
            await rt(msg, "Slow down a little.")
            return
        await handle_item(msg, m.group("a"))
        return
    m = BARE_RE.match(text)
    if m:
        if await gate(update, ctx.bot, msg):
            return
        if m.group("c").lower() == "item":
            await rt(msg, "Usage: /item <id or name>")
        else:
            await rt(msg, f"Usage: /{m.group('c').lower()} <uid>")


async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not msg or duplicate(update):
        return
    if await gate(update, ctx.bot, msg):
        return
    cap = welcome_caption(update.effective_user, ctx.bot.username)
    if PIL_OK:
        try:
            card = await asyncio.to_thread(render_welcome)
        except Exception as e:
            log.warning("welcome card failed: %r", e)
            card = None
        if card and await send_photo(msg, card, cap):
            return
    await rt(msg, cap, parse_mode=ParseMode.HTML)


async def help_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not msg or duplicate(update):
        return
    if await gate(update, ctx.bot, msg):
        return
    await rt(msg, help_text(), parse_mode=ParseMode.HTML)


async def on_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not q or not q.data or not q.message:
        return
    if duplicate(update):
        return
    kind, _, val = q.data.partition(":")
    if kind == "ow":
        await owner_cb(q, val)
        return
    if await gate(update, ctx.bot, q=q):
        return
    if kind in ("dt", "pf", "pt", "pa", "pd", "tl"):
        await track_cb(q, kind, val)
        return
    if limited(q.from_user.id):
        await q.answer("Slow down a little.")
        return
    await q.answer()
    if kind == "r":
        await handle_info(q.message, val, force=True, by=q.from_user.id)
    elif kind == "c":
        await handle_info(q.message, val, by=q.from_user.id)
    elif kind == "ut":
        t = TRACKS.get(val)
        if t and q.from_user.id in t["subs"]:
            t["subs"].remove(q.from_user.id)
            (t.get("off") or {}).pop(str(q.from_user.id), None)
            if not t["subs"]:
                TRACKS.pop(val, None)
            await tstore_save()
            await rt(q.message, bq(f"<b>TRACKING STOPPED</b>\n\n{cp(val)}"), parse_mode=ParseMode.HTML)
        else:
            await rt(q.message, "You're not tracking that UID.")


# ───────────────────────── /track — live profile change alerts (private chat only) ─────────────────────────
UID_RE = re.compile(r"^\d{5,13}$")
TRACK_MIN = float(os.getenv("TRACK_MIN", "5"))
TRACK_MAX = max(TRACK_MIN, float(os.getenv("TRACK_MAX", "10")))
TRACK_IGNORE = [x.strip() for x in os.getenv("TRACK_IGNORE", "").split(",") if x.strip()]  # path fragments to ignore
TRACK_FILE = os.getenv("TRACK_FILE", "tracks.json")
MONGO_URI = os.getenv("MONGO_URI", "")
TRACKS: dict = {}   # uid -> {"subs": [chat ids], "snap": {flat}, "name": str, "fails": int, "due": float, "busy": bool, "warned": bool}
_TASKS: set = set()
_SAVE_LOCK = None
_mcol = None


def _dump():
    return {u: {"subs": t["subs"], "name": t.get("name", ""), "mute": t.get("mute") or [],
                "snap": json.dumps(t.get("snap") or {}, ensure_ascii=False),
                "base": json.dumps(t.get("base") or {}, ensure_ascii=False),
                "since": t.get("since", 0), "n": t.get("n", 0), "last": t.get("last", 0),
                "color": t.get("color", 0), "guild": t.get("guild", ""), "off": t.get("off") or {},
                "gj": t.get("gj", 0), "gl": t.get("gl", 0), "look_due": t.get("look_due", 0),
                "sub_at": t.get("sub_at") or {},
                "log": json.dumps(t.get("log") or [], ensure_ascii=False)}
            for u, t in TRACKS.items()}


async def tstore_load():
    data = {}
    try:
        data = await db.load_tracks()
    except Exception as e:
        log.warning("track load failed: %r", e)
    if not data and DATA.get("tracks"):  # local file was wiped (e.g. redeploy) -> restore the MongoDB backup
        data = DATA["tracks"]
        log.info("tracking restored from the settings backup")
    for u, t in data.items():
        try:
            _snap = json.loads(t.get("snap") or "{}")
            TRACKS[u] = {"subs": [int(x) for x in t["subs"]], "name": t.get("name", ""), "snap": _snap,
                         "base": json.loads(t.get("base") or "{}") or dict(_snap),
                         "since": t.get("since") or time.time(), "n": t.get("n", 0), "last": t.get("last", 0),
                         "color": t.get("color", 0), "guild": t.get("guild", ""), "off": dict(t.get("off") or {}),
                         "gj": t.get("gj", 0), "gl": t.get("gl", 0), "look_due": t.get("look_due", 0),
                         "sub_at": dict(t.get("sub_at") or {}),
                         "log": json.loads(t.get("log") or "[]"),
                         "mute": list(t.get("mute") or []),
                         "fails": 0, "due": time.time() + random.uniform(1, tmax()), "busy": False, "warned": False}
        except Exception:
            continue
    log.info("tracking %d player(s) (%s) | %d premium emoji", len(TRACKS), db.backend(), len(PREMIUM))


async def tstore_save():
    global _SAVE_LOCK
    _SAVE_LOCK = _SAVE_LOCK or asyncio.Lock()
    async with _SAVE_LOCK:
        payload = _dump()
        try:
            await db.save_tracks(payload)
        except Exception as e:
            log.warning("track save failed: %r", e)
        DATA["tracks"] = payload
        STORE.touch()


def trackable(path):
    """Only fields inside the profile sections count. Top-level scalars (API meta such as response time) never do."""
    return ("." in path and not any(f in path for f in TRACK_IGNORE)
            and not path.startswith("captain_basic_info") and path != "clan_basic_info.captain_id")


def flatten_player(js):
    out = {}

    def walk(o, pre):
        if isinstance(o, dict):
            for k, v in o.items():
                walk(v, f"{pre}.{k}" if pre else str(k))
        elif isinstance(o, list):
            if all(not isinstance(x, (dict, list)) for x in o):
                out[pre] = list(o)
            else:
                for i, x in enumerate(o):
                    walk(x, f"{pre}[{i}]")
        else:
            out[pre] = o

    walk(js, "")
    return {k: v for k, v in out.items() if trackable(k)}


def diff_snap(old, new, mute=()):
    ch = []
    for k in list(old) + [k for k in new if k not in old]:
        if not trackable(k) or k in mute:  # also filters snapshots saved by an older run
            continue
        a, b = old.get(k), new.get(k)
        if a != b:
            ch.append((k, a, b))
    return ch


# ───────── premium (custom) emoji — optional ─────────
# Emoji ids come from db.py (imported from emoji.txt, stored in data/ffbot.db). Anything missing falls back to
# the normal emoji, so the bot never breaks. (Custom emoji render only if Telegram allows them for your bot.)
def _load_premium():
    try:
        return db.get_emojis()  # emoji.txt is imported into the DB automatically
    except Exception as e:
        log.warning("premium emoji map ignored: %r", e)
        return {}


PREMIUM = _load_premium()


def em(e: str) -> str:
    i = PREMIUM.get(db.norm(e))
    return f'<tg-emoji emoji-id="{i}">{e}</tg-emoji>' if i else e


# one colour square per tracked player -> every alert is instantly recognisable
DOTS = ["🟦", "🟩", "🟨", "🟧", "🟥", "🟪", "🟫", "⬜"]
SEP = "▬▬▬▬▬▬▬▬▬▬▬▬▬▬"

# alert categories (the user chooses which ones to receive)
# path -> (emoji, label, kind)   kind: ts | num | id | ids | rank | text
TRACK_LABELS = {
    "basic_info.nickname": ("👤", "Name", "text"), "basic_info.level": ("📈", "Level", "num"),
    "basic_info.exp": ("✨", "EXP", "num"), "basic_info.liked": ("❤️", "Likes", "num"),
    "basic_info.rank": ("🏆", "BR Rank", "rank"), "basic_info.ranking_points": ("🏅", "BR Points", "num"),
    "basic_info.max_rank": ("🥇", "BR Max Rank", "rank"), "basic_info.cs_rank": ("⚔️", "CS Rank", "text"),
    "basic_info.cs_ranking_points": ("🎯", "CS Points", "num"), "basic_info.cs_max_rank": ("🥇", "CS Max Rank", "text"),
    "basic_info.banner_id": ("🖼", "Banner", "id"), "basic_info.head_pic": ("🎭", "Head Pic", "id"),
    "basic_info.title": ("🎖", "Title", "id"), "basic_info.badge_id": ("🏷", "Badge", "id"),
    "basic_info.badge_cnt": ("🏷", "Badges", "num"), "basic_info.last_login_at": ("🟢", "Logged in", "ts"),
    "basic_info.weapon_skin_shows": ("🔫", "Weapon Skins", "ids"), "profile_info.avatar_id": ("🧑", "Avatar", "id"),
    "profile_info.equipped_skills": ("🎒", "Equipped Items", "ids"), "profile_info.cosmetic_items": ("🧥", "Cosmetics", "ids"),
    "social_info.social_highlight": ("💬", "Bio", "text"), "clan_basic_info.clan_name": ("🛡", "Guild Name", "text"),
    "clan_basic_info.clan_id": ("🛡", "Guild ID", "text"), "clan_basic_info.clan_level": ("🛡", "Guild Level", "num"),
    "clan_basic_info.current_members": ("🛡", "Members", "num"), "clan_basic_info.max_members": ("🛡", "Capacity", "num"),
    "clan_basic_info.captain_id": ("👑", "Leader changed", "text"), "pet_info.pet_name": ("🐾", "Pet Name", "text"),
    "pet_info.level": ("🐾", "Pet Level", "num"), "pet_info.skin_id": ("🐾", "Pet Skin", "id"),
    "pet_info.selected_skill_id": ("🐾", "Pet Skill", "id"),
}


def _label(path, cat="misc"):
    base = re.sub(r"\[\d+\]", "", path)
    sec, _, key = base.partition(".")
    look = ("basic_info." + key) if sec == "captain_basic_info" else base
    if look in TRACK_LABELS:
        return TRACK_LABELS[look]
    last = key.replace(".", " · ").replace("_", " ").title()
    pre = (sec.replace("_info", "").replace("_", " ").title() + " · ") if cat == "misc" else ""
    return (CAT[cat][0], pre + last, "auto")


def _is_id(v):
    return isinstance(v, int) and not isinstance(v, bool) and v >= 100000 or (isinstance(v, str) and v.isdigit() and len(v) >= 6)


CATS = [
    ("lvl", "📈", "Level & EXP"),
    ("like", "❤️", "Likes"),
    ("login", "🟢", "Login"),
    ("rank", "🏆", "Rank"),
    ("prof", "✏️", "Name & Bio"),
    ("look", "🎒", "Outfit"),
    ("guild", "🛡", "Guild"),
    ("misc", "🔧", "Pet & Other"),
]
CAT = {k: (e, n) for k, e, n in CATS}
CAT_ORDER = {k: i for i, (k, _, _) in enumerate(CATS)}
OUTFIT_SCAN = float(os.getenv("OUTFIT_SCAN", "120"))  # seconds between outfit / character scans


def ic(e: str) -> str:
    """Premium emoji only. If we don't own a premium version, show nothing (no random plain emoji)."""
    return ""  # tracker is emoji-free on purpose (clean, premium look)


def nearest_color(hexcode: str) -> str:
    h = hexcode.lstrip("#")
    r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
    ref = {"red": (221, 46, 68), "orange": (244, 144, 12), "yellow": (253, 203, 88), "green": (120, 177, 89),
           "blue": (85, 172, 238), "purple": (170, 142, 214), "brown": (193, 105, 79), "black": (49, 55, 61), "white": (230, 231, 232)}
    return min(ref, key=lambda k: (ref[k][0] - r) ** 2 + (ref[k][1] - g) ** 2 + (ref[k][2] - b) ** 2)


def frame_strip() -> str:
    n = int(CFG.get("strip_len", 8))
    if n <= 0:
        return ""
    mode = CFG.get("frame", "auto")
    if mode == "auto":  # a new colour every day, cycling through all 9
        now = datetime.now(IST)
        mode = CFG["week"][now.weekday()] or list(COLORS)[now.toordinal() % len(COLORS)]
    return COLORS.get(mode, COLORS["blue"]) * n


def bq(s: str) -> str:
    """The frame every message sits in. Colour strip on top: set by the owner or rotating by weekday."""
    st = frame_strip()
    return f"<blockquote>{st + chr(10) if st else ''}{s}</blockquote>"


def _head(e, n):
    return f"<b>{esc(n.upper())}</b>"


def _offset(t, chat_id):
    return {k for k in (t.get("off") or {}).get(str(chat_id), []) if k in CAT}


def cat_of(path):
    base = re.sub(r"\[\d+\]", "", path)
    sec, _, key = base.partition(".")
    if sec == "clan_basic_info":
        return "guild"
    if sec == "social_info":
        return "prof"
    if sec == "profile_info":
        return "look"
    if sec == "basic_info":
        if key in ("level", "exp"):
            return "lvl"
        if key == "liked":
            return "like"
        if key == "last_login_at":
            return "login"
        if key == "nickname":
            return "prof"
        if key.startswith(("rank", "ranking_", "max_rank", "cs_", "hippo_", "peak_rank", "season")):
            return "rank"
        if key in ("banner_id", "head_pic", "title", "badge_id", "badge_cnt", "weapon_skin_shows"):
            return "look"
    return "misc"


def render_rows(changes, nm, snap):
    """-> [[cat, emoji, label, value_html], ...]  (JSON-safe, also stored in the history log)"""
    out = []
    for p, a, b in changes:
        cat = cat_of(p)
        emo, lab, kind = _label(p, cat)
        if kind == "text" and clean(str(a if a is not None else "")) == clean(str(b if b is not None else "")):
            continue  # only colour codes changed
        if kind == "text":
            ca, cb = clean(str(a if a is not None else "")), clean(str(b if b is not None else ""))
            out.append([cat, emo, lab, f"\n│   Before: {cp(ca[:600] or '—')}\n│   Now:    {cp(cb[:600] or '—')}"])
            continue
        if kind == "ts":
            lab = "Logged in"
            val = cp(tss(b)) + (f"\n│   ↳ Previous: {esc(tss(a))}" if a else "")
        elif isinstance(a, list) or isinstance(b, list):
            la, lb = (a or []), (b or [])
            add, rem = [x for x in lb if x not in la], [x for x in la if x not in lb]
            val = ""
            if add:
                val += "\n│   + " + ", ".join(_tv(x, kind, nm) for x in add[:12])
            if rem:
                val += "\n│   − " + ", ".join(_tv(x, kind, nm) for x in rem[:12])
            if not val:
                val = "\n│   order changed"
        elif a is None:
            val = f"new → {_tv(b, kind, nm)}"
        elif b is None:
            val = f"{_tv(a, kind, nm)} → removed"
        else:
            d = _delta(a, b) if (kind == "num" or (kind == "auto" and not _is_id(a))) else ""
            val = f"{_tv(a, kind, nm)} → {_tv(b, kind, nm)}{d}"
        out.append([cat, emo, lab, val])
    out.sort(key=lambda r: CAT_ORDER.get(r[0], 99))
    return out


def _nogd(v):
    return v in (None, "", 0, "0")


def guild_rows(old, new):
    """Guild events of the tracked player: joined / left / switched (old -> new) / renamed. None = nothing."""
    k = "clan_basic_info."
    o, n = old.get(k + "clan_id"), new.get(k + "clan_id")
    on, nn = clean(str(old.get(k + "clan_name") or "")), clean(str(new.get(k + "clan_name") or ""))
    mem = lambda: cp(f"{new.get(k + 'current_members')}/{new.get(k + 'max_members', '?')}")  # noqa: E731
    if o == n:
        if not _nogd(n) and on and nn and on != nn:  # same guild, new name
            return [["guild", "", "Guild name", f"\n│   Before: {cp(on)}\n│   Now:    {cp(nn)}"]]
        return None
    if _nogd(o) and _nogd(n):
        return None
    if not _nogd(o) and not _nogd(n):  # switched guild
        rows = [["guild", "", "Guild changed", f"\n│   Before: {cp(on or o)}\n│   Now:    {cp(nn or n)}"]]
    elif not _nogd(o):
        rows = [["guild", "", "Left guild", cp(on or o)]]
    else:
        rows = [["guild", "", "Joined guild", cp(nn or n)]]
    if not _nogd(n) and new.get(k + "current_members") is not None:
        rows.append(["guild", "", "Members", mem()])
    return rows


def dot_of(t):
    return "◈"


def _group_html(cat, rows):
    e, n = CAT.get(cat, ("", "Other"))
    lines = [_head(e, n)]
    for i, (_, _, lab, val) in enumerate(rows):
        last = i == len(rows) - 1
        val = str(val).replace("\n│   ", "\n" + ("    " if last else "│   "))
        sep = "" if val.startswith("\n") else ": "
        lines.append(("└" if last else "├") + f" {esc(lab)}{sep}{val}")
    return "\n".join(lines)


def alert_parts(t, uid, rows, now):
    name = clean(t.get("name")) or uid
    head = (f"<b>PROFILE UPDATE</b>  ·  #{t.get('n', 0)}\n"
            f"<b>{esc(name)}</b>\n"
            f"UID {cp(uid)}\n"
            f"{esc(datetime.fromtimestamp(now, IST).strftime('%d %b %Y, %I:%M:%S %p'))}")
    return [bq(p) for p in pack([head] + _groups(rows))]


# ---- full details ("everything that changed so far") ----
SUM_NUM = [
    ("basic_info.level", "Level"), ("basic_info.exp", "EXP"), ("basic_info.liked", "Likes"),
    ("basic_info.badge_cnt", "Badges"), ("basic_info.ranking_points", "BR Points"),
    ("basic_info.cs_ranking_points", "CS Points"), ("pet_info.level", "Pet Level"),
]
SUM_TXT = [
    ("basic_info.nickname", "Name"), ("social_info.social_highlight", "Bio"),
]


def details_parts(t, uid, chat_id=None):
    off = _offset(t, chat_id) if chat_id is not None else set()
    cur, base = t.get("snap") or {}, t.get("base") or {}
    name = clean(t.get("name")) or uid
    lg = cur.get("basic_info.last_login_at")
    head = "\n".join([
        "<b>FULL DETAILS</b>",
        f"<b>{esc(name)}</b>",
        f"├ UID: {cp(uid)}",
        f"├ Tracking since: {cp(tss(t.get('since')) if t.get('since') else '—')} ({esc(ago(t.get('since')))})",
        f"├ Last login: {cp(tss(lg) if lg else '—')}",
        f"├ Changes caught: {cp(t.get('n', 0))}",
        f"└ Last change: {esc(ago(t.get('last')))}",
    ])
    tot = []
    for p, lab in SUM_NUM:
        if cat_of(p) in off:
            continue
        a, b = base.get(p), cur.get(p)
        if a is not None and b is not None and a != b:
            tot.append(f"{esc(lab)}: {cp(indian(a))} → {cp(indian(b))}{_delta(a, b)}")
    for p, lab in SUM_TXT:
        if cat_of(p) in off:
            continue
        a, b = base.get(p), cur.get(p)
        ca, cb = clean(str(a)) if a not in (None, "") else "", clean(str(b)) if b not in (None, "") else ""
        if ca != cb:
            tot.append(f"{esc(lab)}\n│   Before: {cp(ca[:300] or '—')}\n│   Now:    {cp(cb[:300] or '—')}")
    if not tot:
        tot = ["No changes yet. I'm watching."]
    total_txt = _head("", "Total since tracking started") + "\n" + "\n".join(
        ("└ " if i == len(tot) - 1 else "├ ") + x.replace("\n│   ", "\n" + ("    " if i == len(tot) - 1 else "│   "))
        for i, x in enumerate(tot))

    sections = [head, total_txt]
    cl = "clan_basic_info."
    if cur.get(cl + "clan_name") and "guild" not in off:
        gl = [f"Name: {cp(clean(str(cur.get(cl + 'clan_name'))))}",
              f"Members now: {cp(str(cur.get(cl + 'current_members', '?')) + '/' + str(cur.get(cl + 'max_members', '?')))}",
              f"Joined since start: {cp('+' + str(t.get('gj', 0)))}",
              f"Left since start: {cp('−' + str(t.get('gl', 0)))}"]
        sections.append(_head("", "Guild") + "\n" + "\n".join(
            ("└ " if i == len(gl) - 1 else "├ ") + x for i, x in enumerate(gl)))

    entries = []
    for e in (t.get("log") or []):
        rs = [r for r in (e.get("rows") or []) if r[0] in CAT and r[0] not in off]
        if not rs:
            continue
        lines = [f"<b>{esc(datetime.fromtimestamp(e['t'], IST).strftime('%d %b, %I:%M:%S %p'))}</b>"]
        for i, (_, _, lab, val) in enumerate(rs):
            last = i == len(rs) - 1
            v = str(val).replace("\n│   ", "\n" + ("    " if last else "│   "))
            lines.append(("└ " if last else "├ ") + f"{esc(lab)}{'' if v.startswith(chr(10)) else ': '}{v}")
        entries.append("\n".join(lines))
    shown, size = [], 0
    for en in reversed(entries):  # newest first until the message is full
        if size + len(en) > 2400:
            break
        shown.append(en)
        size += len(en) + 2
    shown.reverse()
    hidden = len(entries) - len(shown)
    tl_head = _head("", "Timeline") + (f" <i>(latest {len(shown)}, {hidden} older hidden)</i>" if hidden > 0 else "")
    sections += [tl_head] + (shown or ["Nothing yet."])
    return [bq(p) for p in pack(sections)]


# ---- buttons (plain text, compact) ----
def track_kb(uid):
    return InlineKeyboardMarkup([[InlineKeyboardButton("Details", callback_data=f"dt:{uid}"),
                                  InlineKeyboardButton("Alerts", callback_data=f"pf:{uid}"),
                                  InlineKeyboardButton("Stop", callback_data=f"ut:{uid}")]])


stop_kb = track_kb


def prefs_view(chat_id, uid, intro=True):
    t = TRACKS.get(uid) or {}
    off = _offset(t, chat_id)
    btns = [InlineKeyboardButton(f"{'●' if k not in off else '○'}  {n}", callback_data=f"pt:{uid}:{k}") for k, _, n in CATS]
    rows = [btns[i:i + 2] for i in range(0, len(btns), 2)]
    rows.append([InlineKeyboardButton("All ON", callback_data=f"pa:{uid}:1"),
                 InlineKeyboardButton("All OFF", callback_data=f"pa:{uid}:0")])
    rows.append([InlineKeyboardButton("Done", callback_data=f"pd:{uid}")])
    name = clean(t.get("name")) or uid
    text = bq("<b>ALERT SETTINGS</b>\n"
              f"<b>{esc(name)}</b>\n"
              f"UID {cp(uid)}\n\n"
              "Choose which updates you want to receive.\n"
              "●  ON      ○  OFF\n"
              "Tap a button to switch it.\n\n"
              f"<b>{len(CATS) - len(off)} of {len(CATS)}</b> alerts are ON")
    return text, InlineKeyboardMarkup(rows)


async def send_to(app, uid, chat_id, parts, kb=None, cards=None):
    t = TRACKS.get(uid)
    if not t:
        return

    async def forbidden():
        if chat_id in t["subs"]:  # user blocked the bot / deleted chat -> stop tracking for them
            t["subs"].remove(chat_id)

    if cards:  # new outfit images go ABOVE the message
        try:
            if len(cards) == 1:
                if len(parts) == 1 and len(parts[0]) <= 1024:
                    await app.bot.send_photo(chat_id, cards[0], caption=parts[0], parse_mode=ParseMode.HTML, reply_markup=kb)
                    return
                await app.bot.send_photo(chat_id, cards[0])
            else:
                await app.bot.send_media_group(chat_id, [InputMediaPhoto(c) for c in cards])
        except Forbidden:
            await forbidden()
            return
        except Exception as e:
            log.warning("outfit image send failed: %r", e)
    for i, part in enumerate(parts):
        for attempt in range(2):
            try:
                await app.bot.send_message(chat_id, part, parse_mode=ParseMode.HTML,
                                           reply_markup=kb if i == len(parts) - 1 else None)
                break
            except RetryAfter as e:
                await asyncio.sleep(min(float(getattr(e, "retry_after", 2)), 20))
            except Forbidden:
                await forbidden()
                return
            except Exception as e:
                log.warning("alert send failed: %r", e)
                break


async def notify(app, uid, text_parts):
    """Plain notices (API down / back) to every subscriber."""
    t = TRACKS.get(uid)
    if not t:
        return
    for chat_id in list(t["subs"]):
        await send_to(app, uid, chat_id, [bq(p) for p in text_parts], with_add(track_kb(uid)))
    await _cleanup(uid)


async def notify_changes(app, uid, rows, now, cards=None):
    t = TRACKS.get(uid)
    if not t:
        return
    for chat_id in list(t["subs"]):
        off = _offset(t, chat_id)
        mine_rows = [r for r in rows if r[0] not in off]
        if mine_rows and in_quiet(chat_id):
            continue  # quiet hours: still saved in Details
        if mine_rows:
            ok, warn = alert_allow(chat_id)
            if warn:
                try:
                    await app.bot.send_message(chat_id, bq(warn), parse_mode=ParseMode.HTML)
                except Exception:
                    pass
            if not ok:
                continue  # limit reached: still saved in Details
            use = cards if (cards and any(r[0] == "look" for r in mine_rows)) else None
            await send_to(app, uid, chat_id, alert_parts(t, uid, mine_rows, now), with_add(track_kb(uid)), cards=use)
    await _cleanup(uid)


async def poll_one(app, uid):
    t = TRACKS.get(uid)
    if not t:
        return
    try:
        js = await fetch_once(uid)
    except Exception as e:
        t["fails"] += 1
        DATA["stats"]["api_fail"] = DATA["stats"].get("api_fail", 0) + 1
        if t["fails"] in (1, 5, 30):
            log.warning("track %s fetch failed (%d): %r", uid, t["fails"], e)
        if t["fails"] >= 30 and not t["warned"]:
            t["warned"] = True
            await owner_alert(app.bot, f"The info API has been failing for UID {cp(uid)} (about 13 minutes): {esc(why(e))}", key="api")
            await notify(app, uid, [f"<b>API UNREACHABLE</b>\nUID {cp(uid)}\n\nI can't reach the API right now "
                                    "(the server is not responding). I keep retrying and will message you when it's back."])
        return
    recovered = t["warned"]
    t["fails"], t["warned"] = 0, False
    snap = flatten_player(js)
    b = js.get("basic_info") or {}
    if b.get("nickname"):
        t["name"] = b["nickname"]
    g = (js.get("clan_basic_info") or {}).get("clan_name")
    if g is not None:
        t["guild"] = g
    if recovered:
        await notify(app, uid, [f"<b>API IS BACK</b>\nUID {cp(uid)}\n\nTracking again."])
    if not t.get("snap"):
        t["snap"] = snap
        t.setdefault("base", snap)
        t.setdefault("since", time.time())
        t["look_due"] = time.time() + oscan()
        await tstore_save()
        return
    old = t["snap"]
    now = time.time()
    ck = "clan_basic_info."
    # API hiccup: guild block missing for a single poll must not look like "left the guild"
    if old.get(ck + "clan_id") and not snap.get(ck + "clan_id"):
        t["g_miss"] = t.get("g_miss", 0) + 1
        if t["g_miss"] < 2:
            for k, v in old.items():
                if k.startswith(ck):
                    snap[k] = v
    else:
        t["g_miss"] = 0
    # outfit / character is only scanned every oscan() seconds
    if now < t.get("look_due", 0):
        for k in set(old) | set(snap):
            if cat_of(k) == "look":
                if k in old:
                    snap[k] = old[k]
                else:
                    snap.pop(k, None)
    else:
        t["look_due"] = now + oscan()
    changes = diff_snap(old, snap, t.get("mute") or ())
    hist = t.setdefault("hist", {})
    real = []
    for p, a, b2 in changes:
        h = [x for x in hist.get(p, []) if now - x < 90] + [now]
        hist[p] = h
        if len(h) >= 3 and re.sub(r"\[\d+\]", "", p) not in TRACK_LABELS:  # unknown field that keeps flipping -> API noise
            t.setdefault("mute", []).append(p)
            log.info("track %s: muting noisy field %s", uid, p)
            continue
        real.append((p, a, b2))
    if len(hist) > 200:
        hist.clear()
    # guild: only join / leave / switch and the member count (no name, level, capacity, leader noise)
    real = [c for c in real if not c[0].startswith(ck) or c[0] == ck + "current_members"]
    grows = guild_rows(old, snap)
    gextra, gname = [], ""
    if grows:
        real = [c for c in real if not c[0].startswith(ck)]
    else:
        for p, a, b2 in real:
            if p == ck + "current_members" and isinstance(a, int) and isinstance(b2, int):
                if b2 > a:
                    t["gj"] = t.get("gj", 0) + (b2 - a)
                else:
                    t["gl"] = t.get("gl", 0) + (a - b2)
                gextra = [["guild", "", "Since tracking", cp(f"{t.get('gj', 0)} joined · {t.get('gl', 0)} left")]]
                gname = clean(str(snap.get(ck + "clan_name") or ""))
    if not real and not grows:
        t["snap"] = snap
        await tstore_save()
        return
    nm = await resolve_names(alert_ids(real)) if alert_ids(real) else {}
    rows = (grows or []) + render_rows(real, nm, snap)
    if gextra and gname:  # the guild's name goes on top of the member change
        at = min([i for i, r in enumerate(rows) if r[0] == "guild"] or [0])
        rows.insert(at, ["guild", "", "Guild", cp(gname)])
    for gx in gextra:  # running total goes right under the member count
        at = max([i for i, r in enumerate(rows) if r[0] == "guild"] or [len(rows) - 1]) + 1
        rows.insert(at, gx)
    rows.sort(key=lambda r: CAT_ORDER.get(r[0], 99))
    if not rows:  # e.g. only colour codes changed
        t["snap"] = snap
        await tstore_save()
        return
    # new outfit / character -> render the images (shown above the message)
    cards = []
    img_paths = [p for p, _, _ in real if cat_of(p) == "look" and not p.endswith("badge_cnt")]
    if img_paths and PIL_OK:
        try:
            built = await build_cards_safe(js, await resolve_names(collect_ids(js)))
        except Exception as e:
            log.warning("outfit cards failed: %r", e)
            built = []
        items = any(("equipped_skills" in p or "weapon_skin_shows" in p or "cosmetic" in p) for p in img_paths)
        ident = any(not ("equipped_skills" in p or "weapon_skin_shows" in p or "cosmetic" in p) for p in img_paths)
        if len(built) == 2:
            cards = built if (items and ident) else ([built[1]] if items else [built[0]])
        else:
            cards = built
    t["snap"] = snap
    t["n"] = t.get("n", 0) + 1
    t["last"] = now
    t.setdefault("log", []).append({"t": now, "rows": rows})
    t["log"] = t["log"][-60:]
    await tstore_save()
    await notify_changes(app, uid, rows, now, cards)


def track_list_text(user_id):
    ids = mine(user_id)
    if not ids:
        return bq("<b>NO PLAYERS TRACKED</b>\n\nStart one with <code>/track &lt;uid&gt;</code>"), None
    blocks = [f"<b>TRACKING {len(ids)} OF {lim_txt(user_id)}</b>\nChecked every {tmin():g}–{tmax():g} seconds"]
    kb = []
    for i, u in enumerate(ids, 1):
        t = TRACKS[u]
        off = _offset(t, user_id)
        nm = clean(t.get("name")) or u
        lines = [f"<b>{i}. {esc(nm)}</b>", f"├ UID: {cp(u)}"]
        if "guild" not in off:
            lines.append(f"├ Guild: {esc(clean(t.get('guild') or '') or '—')}")
        lines += [f"├ Changes so far: <b>{t.get('n', 0)}</b>",
                  f"├ Last change: {esc(ago(t.get('last')))}",
                  f"└ Alerts ON: {len(CATS) - len(off)} of {len(CATS)}"]
        blocks.append("\n".join(lines))
        kb.append([InlineKeyboardButton(f"{i}. Details", callback_data=f"dt:{u}"),
                   InlineKeyboardButton("Alerts", callback_data=f"pf:{u}"),
                   InlineKeyboardButton("Stop", callback_data=f"ut:{u}")])
    return bq("\n\n".join(blocks)), InlineKeyboardMarkup(kb)


def tss(t) -> str:
    try:
        return datetime.fromtimestamp(int(t), IST).strftime("%d %b %Y, %I:%M:%S %p")
    except Exception:
        return str(t)


def ago(t) -> str:
    if not t:
        return "—"
    s = int(time.time() - t)
    if s < 60:
        return f"{max(s, 0)}s ago"
    if s < 3600:
        return f"{s // 60}m ago"
    if s < 86400:
        return f"{s // 3600}h {(s % 3600) // 60}m ago"
    return f"{s // 86400}d {(s % 86400) // 3600}h ago"


def _delta(a, b):
    try:
        if isinstance(a, bool) or isinstance(b, bool) or not isinstance(a, (int, float)) or not isinstance(b, (int, float)):
            return ""
        d = b - a
        if d == 0:
            return ""
        return f"  <b>{'▲ +' if d > 0 else '▼ −'}{indian(abs(d))}</b>"
    except Exception:
        return ""


def _tv(v, kind, nm):
    if v is None or v == "":
        return cp("—")
    if kind == "ts":
        return cp(tss(v))
    if kind == "num":
        return cp(indian(v))
    if kind == "rank":
        r = br_rank(v)
        return cp(v) + (f" → {esc(r)}" if r else "")
    if kind == "text" and isinstance(v, str):
        return cp(clean(v)[:600])
    n = nm.get(str(v), "") if (kind in ("id", "ids") or (kind == "auto" and _is_id(v))) else ""
    return cp(str(v)[:140]) + (f" → {esc(n)}" if n else "")


def alert_ids(changes):
    ids = []
    for p, a, b in changes:
        for v in (a if isinstance(a, list) else [a]) + (b if isinstance(b, list) else [b]):
            if _is_id(v) and str(v) not in ids:
                ids.append(str(v))
    return ids[:24]


def _groups(rows):
    out, cur, buf = [], None, []
    for r in rows:
        if r[0] != cur and buf:
            out.append(_group_html(cur, buf))
            buf = []
        cur = r[0]
        buf.append(r)
    if buf:
        out.append(_group_html(cur, buf))
    return out


# ---- full details ("everything that changed so far") ----
# ---- buttons ----
async def _cleanup(uid):
    t = TRACKS.get(uid)
    if t is not None and not t["subs"]:
        TRACKS.pop(uid, None)
        await tstore_save()


async def fetch_once(uid):
    """One quick fetch (no retries, no cache read) for the tracker."""
    r = await http().get(INFO_API, params={"uid": uid}, headers={"Cache-Control": "no-cache"}, timeout=15)
    r.raise_for_status()
    js = r.json()
    if not (isinstance(js, dict) and js.get("basic_info")):
        raise ValueError("no data")
    PLAYER_CACHE[uid] = (time.time(), js)
    trim(PLAYER_CACHE, 300)
    return js


async def track_loop(app):
    sem = asyncio.Semaphore(6)

    async def run(uid):
        try:
            async with sem:
                await poll_one(app, uid)
        except Exception as e:
            log.warning("track poll crashed %s: %r", uid, e)
        finally:
            t = TRACKS.get(uid)
            if t:
                t["busy"] = False
                t["due"] = time.time() + (random.uniform(tmin(), tmax()) if t["fails"] < 5 else 30)

    while True:
        now = time.time()
        for uid, t in list(TRACKS.items()):
            if CFG.get("paused"):
                break
            if not t.get("busy") and t.get("due", 0) <= now:
                t["busy"] = True
                task = asyncio.create_task(run(uid))
                _TASKS.add(task)
                task.add_done_callback(_TASKS.discard)
        await asyncio.sleep(1)


TRACK_RE = re.compile(r"^\s*/(?P<c>track|untrack|tracklist)(?:@(?P<b>\w+))?(?:\s+(?P<a>.+))?\s*$", re.I | re.S)


def mine(user_id):
    return [u for u, t in TRACKS.items() if user_id in t["subs"]]


async def track_cb(q, kind, val):
    """Inline-button handlers for the tracker. Never rate-limited (they are quick taps)."""
    user = q.from_user.id
    if kind == "tl":
        await q.answer()
        text, kb = track_list_text(user)
        await q.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        return
    uid, _, rest = val.partition(":")
    t = TRACKS.get(uid)
    if not t or user not in t["subs"]:
        await q.answer("You're not tracking this UID.", show_alert=True)
        return
    if kind == "dt":
        await q.answer()
        parts = details_parts(t, uid, user)
        for i, part in enumerate(parts):
            await q.message.reply_text(part, parse_mode=ParseMode.HTML,
                                       reply_markup=with_add(track_kb(uid)) if i == len(parts) - 1 else None)
        return
    if kind == "pf":
        await q.answer()
        text, kb = prefs_view(user, uid)
        await q.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        return
    off = t.setdefault("off", {}).setdefault(str(user), [])
    toast = ""
    if kind == "pt" and rest in CAT:
        if rest in off:
            off.remove(rest)
            toast = f"{CAT[rest][1]}: ON"
        else:
            off.append(rest)
            toast = f"{CAT[rest][1]}: OFF"
    elif kind == "pa":
        off[:] = [] if rest == "1" else [k for k, _, _ in CATS]
        toast = "All ON" if rest == "1" else "All OFF"
    elif kind == "pd":
        await tstore_save()
        on = [n for k, _, n in CATS if k not in _offset(t, user)]
        await q.answer("Saved")
        body = "\n".join(f"●  {esc(x)}" for x in on) if on else "(nothing, all alerts are OFF)"
        try:
            await q.message.edit_text(bq(f"<b>SAVED</b>\n<b>{esc(clean(t.get('name')) or uid)}</b>\nAlerts you will receive:\n\n{body}"),
                                      parse_mode=ParseMode.HTML, reply_markup=track_kb(uid))
        except Exception:
            pass
        return
    await tstore_save()
    await q.answer(toast)
    text, kb = prefs_view(user, uid)
    try:
        await q.message.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    except Exception as e:
        log.info("prefs edit skipped: %r", e)


def _free_color():
    used = {t.get("color") for t in TRACKS.values()}
    for i in range(len(DOTS)):
        if i not in used:
            return i
    return len(TRACKS) % len(DOTS)


async def handle_track(update, ctx, msg, cmd, arg):
    if msg.chat.type != ChatType.PRIVATE:
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("Open private chat", url=f"https://t.me/{ctx.bot.username}")]])
        await rt(msg, bq("<b>PRIVATE CHAT ONLY</b>\n\nTracking works only in my private chat."), parse_mode=ParseMode.HTML, reply_markup=kb)
        return
    user = update.effective_user.id
    a = (arg or "").split()
    word = a[0].lower() if a else ""
    if cmd == "tracklist" or (cmd == "track" and (not a or word in ("list", "ls"))):
        text, kb = track_list_text(user)
        await rt(msg, text, parse_mode=ParseMode.HTML, reply_markup=kb)
        return
    if cmd == "untrack" or word in ("off", "stop", "remove", "del", "delete"):
        rest = a[1:] if cmd == "track" else a
        if not rest:
            text, kb = track_list_text(user)
            await rt(msg, text + "\n<i>Stop one: /untrack &lt;uid&gt; · all: /untrack all</i>", parse_mode=ParseMode.HTML, reply_markup=kb)
            return
        targets = mine(user) if rest[0].lower() == "all" else [rest[0]]
        done = []
        for u in targets:
            if u in TRACKS and user in TRACKS[u]["subs"]:
                TRACKS[u]["subs"].remove(user)
                (TRACKS[u].get("off") or {}).pop(str(user), None)
                if not TRACKS[u]["subs"]:
                    TRACKS.pop(u, None)
                done.append(u)
        if done:
            await tstore_save()
        await rt(msg, bq(f"<b>TRACKING STOPPED</b>\n\n{', '.join(cp(u) for u in done)}") if done else "You weren't tracking that UID.", parse_mode=ParseMode.HTML)
        return
    uid = word
    if not UID_RE.match(uid):
        await rt(msg, "Usage: <code>/track &lt;uid&gt;</code>", parse_mode=ParseMode.HTML)
        return
    if limited(user):
        await rt(msg, "Slow down a little.")
        return
    if user in (TRACKS.get(uid) or {}).get("subs", []):
        await rt(msg, bq(f"<b>ALREADY TRACKING</b>\n\nUID {cp(uid)}"), parse_mode=ParseMode.HTML, reply_markup=track_kb(uid))
        return
    if uid_blocked(uid):
        await rt(msg, "<b>UID BLOCKED</b>\n\nThis UID can't be searched or tracked.", parse_mode=ParseMode.HTML)
        return
    if len(mine(user)) >= limit_for(user):
        cur = mine(user)
        kb = InlineKeyboardMarkup([[InlineKeyboardButton(f"Stop {clean(TRACKS[u].get('name')) or u}"[:40], callback_data=f"ut:{u}")] for u in cur])
        await rt(msg, f"<b>TRACK LIMIT REACHED</b>\n\nYou can track up to <b>{lim_txt(user)}</b> players and you already track {len(cur)}.\nStop one below, then send /track {uid} again.\nNeed more? Ask the owner for premium.", parse_mode=ParseMode.HTML, reply_markup=kb)
        return
    if uid not in TRACKS and len(TRACKS) >= int(CFG["limit_total"]):
        await rt(msg, "The tracker is full right now. Please try again later.")
        return
    await action(msg, ChatAction.TYPING)
    try:
        js = await fetch_once(uid)
    except Exception as e:
        await rt(msg, fail_text(e))
        return
    b = js.get("basic_info") or {}
    snap = flatten_player(js)
    now = time.time()
    t = TRACKS.setdefault(uid, {"subs": [], "snap": snap, "base": dict(snap), "since": now, "n": 0, "log": [], "off": {},
                                "gj": 0, "gl": 0, "look_due": now + oscan(),
                                "color": _free_color(), "guild": (js.get("clan_basic_info") or {}).get("clan_name", ""),
                                "name": b.get("nickname", ""), "fails": 0,
                                "due": now + random.uniform(tmin(), tmax()), "busy": False, "warned": False})
    if user not in t["subs"]:
        t["subs"].append(user)
    t.setdefault("sub_at", {})[str(user)] = now
    await tstore_save()
    cur_login = snap.get("basic_info.last_login_at")
    await rt(msg, bq("<b>TRACKING STARTED</b>\n"
                     f"<b>{esc(clean(b.get('nickname')) or uid)}</b>\n\n"
                     f"├ UID: {cp(uid)}\n"
                     f"├ Guild: {esc(clean(t.get('guild') or '') or '—')}\n"
                     f"├ Last login: {cp(tss(cur_login) if cur_login else '—')}\n"
                     f"├ Profile check: every <b>{tmin():g}–{tmax():g} s</b>\n"
                     f"└ Outfit &amp; character check: every <b>{oscan() / 60:g} min</b>"),
             parse_mode=ParseMode.HTML, reply_markup=track_kb(uid))
    text, kb = prefs_view(user, uid)  # ask permission: which alerts do you want?
    await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


# ───────────────────────── owner / admin system ─────────────────────────
def _int_env(name, default):
    try:
        return int(os.getenv(name, "") or default)
    except ValueError:
        return default


OWNER_ID = _int_env("OWNER_ID", 8536757095)
DATA_DIR = os.getenv("DATA_DIR", "data")
CFG_FILE = os.path.join(DATA_DIR, "ffbot_cfg.json")
MONGO_DB = os.getenv("MONGO_DB", "ffbot")
BOOT = time.time()

COLORS = {"red": "🟥", "orange": "🟧", "yellow": "🟨", "green": "🟩", "blue": "🟦",
          "purple": "🟪", "brown": "🟫", "black": "⬛", "white": "⬜"}
DAYS = ["mon", "tue", "wed", "thu", "fri", "sat", "sun"]

DEF_CFG = {
    "maint": False, "maint_msg": "The bot is under maintenance right now. Please try again a little later.",
    "paused": False,                                   # live tracking paused for everyone
    "limit_default": _int_env("MAX_TRACKS_PER_USER", 2), "limit_users": {},
    "limit_total": _int_env("MAX_TRACKS_TOTAL", 40),
    "search_daily": 100, "search_users": {},            # searches per user per day (0 = unlimited) + per-user overrides
    "alert_daily": 50, "alert_users": {},              # tracking alerts per user in 24 hours (0 = unlimited) + overrides
    "track_min": TRACK_MIN, "track_max": TRACK_MAX,    # seconds between profile checks (random in this range)
    "outfit_scan": OUTFIT_SCAN,                        # seconds between outfit / banner / avatar checks
    "force_join": "",                                  # @channel users must join first
    "welcome": "",                                     # custom welcome template (empty = default)
    "frame": "auto",                                   # auto = colour by weekday, or one fixed colour
    "strip_len": 8,                                    # coloured strip on top of every frame (0 = none)
    "week": ["", "", "", "", "", "", ""],               # per-weekday colour override ("" = daily rotation)
    "limit_premium": 5, "premium_days": 30, "newuser_alert": True,
    "_v": 3,
}
CFG: dict = json.loads(json.dumps(DEF_CFG))
DATA: dict = {"users": {}, "bans": [], "blocked": {}, "hist": {}, "quiet": {}, "premium": {}, "premium_n": {}, "alerts": {}, "alert_warn": {},
              "daily": {"d": "", "c": {}}, "stats": {"searches": 0, "api_fail": 0}, "tracks": None}


class Store:
    """Owner settings, users, bans, history ... kept in a JSON file and, when MONGO_URI is set, in MongoDB too
    (newest copy wins on start). Mongo failing never breaks the bot."""

    def __init__(self):
        self.dirty = False
        self.col = None

    async def load(self):
        best = None
        try:
            with open(CFG_FILE, encoding="utf-8") as f:
                best = json.load(f)
        except Exception:
            pass
        if MONGO_URI:
            try:
                from motor.motor_asyncio import AsyncIOMotorClient

                self.col = AsyncIOMotorClient(MONGO_URI, serverSelectionTimeoutMS=8000)[MONGO_DB]["cfg"]
                d = await asyncio.wait_for(self.col.find_one({"_id": "main"}), 12)
                if d and d.get("data"):
                    m = json.loads(d["data"])
                    if not best or m.get("_ts", 0) >= best.get("_ts", 0):
                        best = m
            except Exception as e:
                log.warning("MongoDB unavailable (%r) - using the local file", e)
                self.col = None
        if best:
            CFG.update(best.get("cfg") or {})
            for k in DATA:
                if k in best and best[k] is not None:
                    DATA[k] = best[k]
        if CFG.get("_v", 0) < 3:  # older saved settings: bring back the daily colour rotation + strip
            CFG["week"], CFG["strip_len"], CFG["_v"] = list(DEF_CFG["week"]), 8, 3
        if not isinstance(CFG.get("week"), list) or len(CFG["week"]) != 7:
            CFG["week"] = list(DEF_CFG["week"])
        log.info("settings loaded (%s) | %d users", "file + MongoDB" if self.col is not None else "file", len(DATA["users"]))

    def touch(self):
        self.dirty = True

    async def save(self):
        self.dirty = False
        txt = json.dumps({"_ts": time.time(), "cfg": CFG, **DATA}, ensure_ascii=False)

        def write():
            os.makedirs(DATA_DIR, exist_ok=True)
            tmp = CFG_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                f.write(txt)
            os.replace(tmp, CFG_FILE)

        try:
            await asyncio.to_thread(write)
        except Exception as e:
            log.warning("settings file save failed: %r", e)
        if self.col is not None:
            try:
                await asyncio.wait_for(self.col.replace_one({"_id": "main"}, {"_id": "main", "data": txt, "ts": time.time()}, upsert=True), 12)
            except Exception as e:
                log.warning("MongoDB save failed: %r", e)


STORE = Store()


async def premium_loop(app):
    """Reminds a premium user one day before it ends; when it ends, keeps their oldest trackings up to the normal
    limit and stops the rest (they are told which)."""
    while True:
        await asyncio.sleep(600)
        try:
            await premium_check(app.bot)
        except Exception as e:
            log.warning("premium loop: %r", e)


async def premium_check(bot):
    now = time.time()
    for u, e in list(DATA["premium"].items()):
        stage = DATA["premium_n"].get(u)
        uid = int(u)
        if e > now and e - now < 86400 and stage != "soon":
            DATA["premium_n"][u] = "soon"
            STORE.touch()
            try:
                await bot.send_message(uid, bq(f"<b>PREMIUM ENDS SOON</b>\n\nYour premium ends on <b>{datetime.fromtimestamp(e, IST).strftime('%d %b %Y, %I:%M %p')}</b>. After that your track limit goes back to <b>{CFG['limit_default']}</b>."), parse_mode=ParseMode.HTML)
            except Exception:
                pass
        elif e <= now:
            DATA["premium"].pop(u, None)
            DATA["premium_n"].pop(u, None)
            STORE.touch()
            mine_ids = sorted(mine(uid), key=lambda x: (TRACKS[x].get("sub_at") or {}).get(u) or TRACKS[x].get("since") or 0)
            cut = mine_ids[limit_for(uid):]
            for x in cut:
                t = TRACKS[x]
                if uid in t["subs"]:
                    t["subs"].remove(uid)
                if not t["subs"]:
                    TRACKS.pop(x, None)
            if cut:
                await tstore_save()
            msg = f"<b>PREMIUM ENDED</b>\n\nYour track limit is back to <b>{lim_txt(uid)}</b>."
            if cut:
                msg += "\nStopped tracking (newest first): " + ", ".join(cp(x) for x in cut)
            try:
                await bot.send_message(uid, bq(msg), parse_mode=ParseMode.HTML)
            except Exception:
                pass


async def store_loop():
    while True:
        await asyncio.sleep(5)
        if STORE.dirty:
            try:
                await STORE.save()
            except Exception as e:
                log.warning("store loop: %r", e)


# ---- small helpers ----
def is_owner(uid) -> bool:
    return uid is not None and int(uid) == OWNER_ID


def today() -> str:
    return datetime.now(IST).strftime("%Y-%m-%d")


UNLIMITED = 10 ** 6


def premium_until(user) -> float:
    e = (DATA.get("premium") or {}).get(str(user), 0)
    return e if e > time.time() else 0


def limit_for(user) -> int:
    if is_owner(user):
        return UNLIMITED
    try:
        base = int(CFG["limit_users"].get(str(user), CFG["limit_default"]))
    except Exception:
        base = int(CFG["limit_default"])
    return max(base, int(CFG.get("limit_premium", 5))) if premium_until(user) else base


def lim_txt(user) -> str:
    n = limit_for(user)
    return "Unlimited" if n >= UNLIMITED else str(n)


def uname(uid) -> str:
    r = DATA["users"].get(str(uid)) or {}
    n = r.get("n") or ""
    return n + (f" @{r['u']}" if r.get("u") else "") if n else str(uid)


def note_user(user, chat_type="") -> bool:
    new = str(user.id) not in DATA["users"]
    r = DATA["users"].setdefault(str(user.id), {"t": time.time(), "s": 0})
    n = " ".join(x for x in (getattr(user, "first_name", "") or "", getattr(user, "last_name", "") or "") if x)
    if n:
        r["n"] = n
    r["u"] = getattr(user, "username", None) or ""
    r["l"] = time.time()
    if chat_type == "private":
        r["dm"] = True
    STORE.touch()
    return new


_NOTE: dict = {}


def once(key, secs=20) -> bool:
    now = time.time()
    if now - _NOTE.get(key, 0) < secs:
        return False
    _NOTE[key] = now
    trim(_NOTE, 2000)
    return True


async def owner_alert(bot, text, key="x", secs=120):
    if not once(("oa", key), secs):
        return
    try:
        await bot.send_message(OWNER_ID, bq(f"<b>OWNER ALERT</b>\n\n{text}"), parse_mode=ParseMode.HTML)
    except Exception:
        pass


def tmin() -> float:
    return max(1.0, float(CFG.get("track_min", 5)))


def tmax() -> float:
    return max(tmin(), float(CFG.get("track_max", 10)))


def oscan() -> float:
    return max(10.0, float(CFG.get("outfit_scan", 120)))


def uptime() -> str:
    s = int(time.time() - BOOT)
    return f"{s // 86400}d {(s % 86400) // 3600}h {(s % 3600) // 60}m"


def uid_blocked(uid) -> bool:
    return str(uid) in DATA["blocked"]


def in_quiet(chat_id) -> bool:
    q = DATA["quiet"].get(str(chat_id))
    if not q:
        return False
    s, e = int(q[0]), int(q[1])
    h = datetime.now(IST).hour
    return (s <= h < e) if s < e else (h >= s or h < e)


# ---- force join ----
MEMBER: dict = {}


def join_url():
    ch = CFG["force_join"]
    return ch if ch.startswith("http") else f"https://t.me/{ch.lstrip('@')}"


async def is_member(bot, user) -> bool:
    if not CFG["force_join"]:
        return True
    if time.time() - MEMBER.get(user, 0) < 300:
        return True
    try:
        cm = await bot.get_chat_member(CFG["force_join"], user)
        ok = str(getattr(cm, "status", "")) not in ("left", "kicked")
    except Exception as e:  # bot is not admin there / wrong name -> don't lock everyone out
        log.warning("force-join check failed: %r", e)
        await owner_alert(bot, f"Force-join check failed for {esc(CFG['force_join'])}. Make me an admin of that channel.", key="fj")
        return True
    if ok:
        MEMBER[user] = time.time()
        trim(MEMBER, 5000)
    return ok


async def gate(update, bot, msg=None, q=None) -> bool:
    """True = stop here (banned / maintenance / must join). The owner always passes."""
    user = update.effective_user
    if not user:
        return False
    msg = msg or (q.message if q else None)
    new = note_user(user, str(getattr(getattr(msg, "chat", None), "type", "")))
    if new and CFG.get("newuser_alert") and not is_owner(user.id):
        try:
            await bot.send_message(OWNER_ID, bq(f"<b>NEW USER</b>\n\n{esc(uname(user.id))}\nID {cp(user.id)} · total users {len(DATA['users'])}"), parse_mode=ParseMode.HTML)
        except Exception:
            pass
    if is_owner(user.id):
        return False
    kind = text = kb = None
    if user.id in DATA["bans"]:
        kind, text = "ban", "<b>ACCESS DENIED</b>\n\nYou are banned from using this bot."
    elif CFG["maint"]:
        kind, text = "maint", f"<b>MAINTENANCE</b>\n\n{esc(CFG['maint_msg'])}"
    elif CFG["force_join"] and not await is_member(bot, user.id):
        kind = "join"
        text = f"<b>JOIN FIRST</b>\n\nPlease join {esc(CFG['force_join'])} to use this bot, then send your command again."
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("Join channel", url=join_url())]])
    if not kind:
        return False
    if q:
        try:
            await q.answer(re.sub(r"<[^>]+>", "", text.split("\n\n")[-1])[:190], show_alert=True)
        except Exception:
            pass
    elif msg and once((user.id, kind), 15):
        await rt(msg, text, add=False, parse_mode=ParseMode.HTML, reply_markup=kb)
    return True


# ---- searches: block list, daily limit, history ----
def search_limit_for(user) -> int:
    try:
        return int(CFG["search_users"].get(str(user), CFG["search_daily"]))
    except Exception:
        return int(CFG["search_daily"])


def _used_today(user) -> int:
    d = DATA["daily"]
    if d.get("d") != today():
        d["d"], d["c"] = today(), {}
    return d["c"].get(str(user), 0)


async def search_ok(msg, by, uid) -> bool:
    """Before a lookup: blocked UID / daily limit. Nothing is counted or saved yet."""
    uid = str(uid)
    if uid_blocked(uid):
        await rt(msg, "<b>UID BLOCKED</b>\n\nThis UID can't be searched or tracked.", parse_mode=ParseMode.HTML)
        return False
    if by is not None and not is_owner(by):
        lim = search_limit_for(by)
        if lim > 0 and _used_today(by) >= lim:
            await rt(msg, f"<b>DAILY LIMIT REACHED</b>\n\nYou can do <b>{lim}</b> searches per day. It resets at midnight (IST).", parse_mode=ParseMode.HTML)
            return False
    return True


def search_done(by, uid):
    """After a SUCCESSFUL lookup: count it and remember it in the history (wrong UIDs never get here)."""
    if by is None:
        return
    uid = str(uid)
    if not is_owner(by):
        _used_today(by)
        DATA["daily"]["c"][str(by)] = DATA["daily"]["c"].get(str(by), 0) + 1
    DATA["stats"]["searches"] = DATA["stats"].get("searches", 0) + 1
    r = DATA["users"].setdefault(str(by), {"t": time.time(), "s": 0})
    r["s"] = r.get("s", 0) + 1
    h = DATA["hist"].setdefault(str(by), [])
    if uid in h:
        h.remove(uid)
    h.insert(0, uid)
    del h[10:]
    STORE.touch()


# ---- tracking alerts: per-user limit in any 24 hours ----
def alert_limit_for(user) -> int:
    if is_owner(user):
        return 0
    try:
        return int(CFG["alert_users"].get(str(user), CFG["alert_daily"]))
    except Exception:
        return int(CFG["alert_daily"])


def alerts_used(user) -> list:
    now = time.time()
    lst = [x for x in DATA["alerts"].get(str(user), []) if now - x < 86400]
    DATA["alerts"][str(user)] = lst
    return lst


def alert_allow(user):
    """(allowed, warning text or None). Counts the alert when allowed."""
    lim = alert_limit_for(user)
    if lim <= 0:
        return True, None
    lst = alerts_used(user)
    now = time.time()
    if len(lst) >= lim:
        w = DATA["alert_warn"].get(str(user), 0)
        warn = None
        if w < lst[0]:  # not warned yet in this window
            DATA["alert_warn"][str(user)] = now
            back = datetime.fromtimestamp(lst[0] + 86400, IST).strftime("%d %b, %I:%M %p")
            warn = (f"<b>ALERT LIMIT REACHED</b>\n\nYou have received <b>{lim}</b> alerts in the last 24 hours, so new alerts are paused.\n"
                    f"They start again around <b>{esc(back)}</b>.\nEverything is still saved: open Details to see what changed.\nNeed more? Ask the owner.")
            STORE.touch()
        return False, warn
    lst.append(now)
    STORE.touch()
    return True, None


# ---- user commands ----
USER_RE = re.compile(r"^\s*/(?P<c>history|quiet|plan)(?:@(?P<b>\w+))?(?:\s+(?P<a>.+))?\s*$", re.I | re.S)


async def user_cmd(update, ctx, msg, cmd, arg):
    user = update.effective_user.id
    a = (arg or "").split()
    if cmd == "history":
        h = DATA["hist"].get(str(user)) or []
        if not h:
            await rt(msg, "<b>SEARCH HISTORY</b>\n\nNothing yet. Try /info &lt;uid&gt;", parse_mode=ParseMode.HTML)
            return
        body = "\n".join(("└ " if i == len(h) - 1 else "├ ") + cp(u) for i, u in enumerate(h))
        btns = [InlineKeyboardButton(u, callback_data=f"c:{u}") for u in h[:6]]
        kb = InlineKeyboardMarkup([btns[i:i + 3] for i in range(0, len(btns), 3)])
        await rt(msg, f"<b>SEARCH HISTORY</b>\nYour last {len(h)} searches\n\n{body}", parse_mode=ParseMode.HTML, reply_markup=kb)
    elif cmd == "quiet":
        if a and a[0].lower() in ("off", "stop", "none"):
            DATA["quiet"].pop(str(user), None)
            STORE.touch()
            await rt(msg, "<b>QUIET HOURS OFF</b>\n\nYou will get tracking alerts all day.", parse_mode=ParseMode.HTML)
        elif len(a) == 2 and all(x.isdigit() and 0 <= int(x) <= 23 for x in a):
            DATA["quiet"][str(user)] = [int(a[0]), int(a[1])]
            STORE.touch()
            await rt(msg, f"<b>QUIET HOURS SET</b>\n\nNo tracking alerts from <b>{int(a[0]):02d}:00</b> to <b>{int(a[1]):02d}:00</b> (IST).\nChanges are still saved in Details.", parse_mode=ParseMode.HTML)
        else:
            q = DATA["quiet"].get(str(user))
            cur = f"Now: {int(q[0]):02d}:00 to {int(q[1]):02d}:00 (IST)" if q else "Now: off"
            await rt(msg, f"<b>QUIET HOURS</b>\n\nMute tracking alerts at night.\n<code>/quiet 23 7</code>  mutes 11 PM to 7 AM\n<code>/quiet off</code>  turns it off\n\n{cur}", parse_mode=ParseMode.HTML)
    else:  # plan
        lim = search_limit_for(user)
        used = (DATA["daily"].get("c") or {}).get(str(user), 0) if DATA["daily"].get("d") == today() else 0
        left = "unlimited" if lim <= 0 or is_owner(user) else f"{max(lim - used, 0)} of {lim} left today"
        pu = premium_until(user)
        prem = f"├ Premium: until <b>{datetime.fromtimestamp(pu, IST).strftime('%d %b %Y')}</b>\n" if pu else ""
        al = alert_limit_for(user)
        al_t = "unlimited" if al <= 0 else f"{len(alerts_used(user))} of {al} used in the last 24 hours"
        await rt(msg, f"<b>YOUR PLAN</b>\n\n{prem}├ Tracking: up to <b>{lim_txt(user)}</b> players ({len(mine(user))} used)\n├ Searches: {left}\n└ Tracking alerts: {al_t}", parse_mode=ParseMode.HTML)


# ---- owner commands ----
OWN_RE = re.compile(r"^\s*/(?P<c>panel|admin|maint|blockuid|unblockuid|blocklist|ban|unban|banlist|limit|searchlimit|trackpause|broadcast|stats|tracked|forcestop|forcejoin|framecolor|framestrip|setwelcome|welcome|premium|unpremium|premiumlist|user|backup|restore|ping|newuseralert|alertlimit|trackspeed|outfitscan)(?:@(?P<b>\w+))?(?:\s+(?P<a>.+))?\s*$", re.I | re.S)


def admin_help():
    return ("<b>OWNER COMMANDS</b>\n\n"
            "<b>Control</b>\n"
            "/panel — live status with switches\n"
            "/maint on [message] · /maint off\n"
            "/trackpause on|off — pause all live tracking\n"
            "/forcejoin @channel · /forcejoin off\n\n"
            "<b>Block</b>\n"
            "/blockuid &lt;uid&gt; [reason] · /unblockuid &lt;uid&gt; · /blocklist\n"
            "/ban &lt;user id&gt; (or reply) · /unban &lt;user id&gt; · /banlist\n\n"
            "<b>Premium</b>\n"
            "/premium &lt;user id&gt; [days] — track limit 5 for 30 days (extends if already premium)\n"
            "/unpremium &lt;user id&gt; · /premiumlist\n\n"
            "<b>Limits</b>\n"
            "/limit — show · /limit &lt;n&gt; default tracks per user\n"
            "/limit &lt;user id&gt; &lt;n&gt; or reset · /limit premium &lt;n&gt; · /limit total &lt;n&gt;\n"
            "/searchlimit &lt;n&gt; — searches per user per day (0 = unlimited)\n"
            "/searchlimit &lt;user id&gt; &lt;n|reset&gt; — one user\n"
            "/alertlimit &lt;n&gt; — tracking alerts per user in 24 hours (default 50, 0 = unlimited)\n"
            "/alertlimit &lt;user id&gt; &lt;n|reset&gt; — one user\n"
            "/trackspeed &lt;min&gt; &lt;max&gt; — seconds between profile checks (default 5 10)\n"
            "/outfitscan &lt;seconds&gt; — outfit, banner and avatar check (default 120)\n\n"
            "<b>Look</b>\n"
            "/framecolor — show · auto (new colour every day, 9 in turn) · a colour name · a hex code like ff69b4\n"
            "/framecolor mon blue — colour of one weekday (mon…sun) · /framecolor mon auto clears it\n"
            "/framestrip &lt;0-16&gt; — length of the colour strip (0 = none)\n"
            "/setwelcome &lt;text&gt; · /setwelcome reset · /welcome — shows current\n"
            "Welcome fields: {name} {first} {mention} {id} {limit} {searches}\n\n"
            "<b>Safety</b>\n"
            "/backup — sends you a file with everything · /restore (reply to that file)\n"
            "/ping — is the API up, storage status, uptime\n"
            "/newuseralert on|off — DM when a new user starts the bot\n\n"
            "<b>Info</b>\n"
            "/stats · /tracked — who tracks whom, and since when\n"
            "/user &lt;user id&gt; — one user: what they track, plan, searches\n"
            "/forcestop &lt;uid&gt;\n"
            "/broadcast &lt;text&gt; (or reply to a message)")


def panel_view():
    n_tr = len(TRACKS)
    subs = sum(len(t["subs"]) for t in TRACKS.values())
    mode = CFG["frame"]
    lines = [
        "<b>OWNER PANEL</b>", "",
        f"├ Maintenance: <b>{'ON' if CFG['maint'] else 'OFF'}</b>",
        f"├ Live tracking: <b>{'PAUSED' if CFG['paused'] else 'RUNNING'}</b>",
        f"├ Default track limit: <b>{CFG['limit_default']}</b> per user",
        f"├ Searches per day: <b>{CFG['search_daily'] or 'unlimited'}</b> · alerts per 24 h: <b>{CFG['alert_daily'] or 'unlimited'}</b>",
        f"├ Check speed: <b>{tmin():g}–{tmax():g} s</b> · outfit/banner/avatar: <b>{oscan():g} s</b>",
        f"├ Force join: <b>{esc(CFG['force_join']) or 'off'}</b>",
        f"├ Frame colour: <b>{esc(mode)}</b> · strip {CFG['strip_len']}",
        f"├ Users: <b>{len(DATA['users'])}</b> · premium {sum(1 for e in DATA['premium'].values() if e > time.time())} · banned {len(DATA['bans'])} · blocked UIDs {len(DATA['blocked'])}",
        f"└ Tracking: <b>{n_tr}</b> players · {subs} watchers",
        "", "All commands: /admin",
    ]
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton(f"Maintenance: {'ON' if CFG['maint'] else 'OFF'}", callback_data="ow:maint"),
         InlineKeyboardButton(f"Tracking: {'PAUSED' if CFG['paused'] else 'ON'}", callback_data="ow:pause")],
        [InlineKeyboardButton(f"Frame: {mode}", callback_data="ow:frame"),
         InlineKeyboardButton(f"Strip: {CFG['strip_len']}", callback_data="ow:strip")],
        [InlineKeyboardButton("Stats", callback_data="ow:stats"), InlineKeyboardButton("Refresh", callback_data="ow:refresh")],
    ])
    return "\n".join(lines), kb


def stats_text():
    users = DATA["users"]
    dm = sum(1 for r in users.values() if r.get("dm"))
    today_n = sum((DATA["daily"].get("c") or {}).values()) if DATA["daily"].get("d") == today() else 0
    subs = sum(len(t["subs"]) for t in TRACKS.values())
    return ("<b>STATS</b>\n\n"
            f"├ Users: <b>{len(users)}</b> ({dm} can receive DMs)\n"
            f"├ Searches today: <b>{today_n}</b> · total {DATA['stats'].get('searches', 0)}\n"
            f"├ Tracking: <b>{len(TRACKS)}</b> players · {subs} watchers\n"
            f"├ Banned users: {len(DATA['bans'])} · blocked UIDs: {len(DATA['blocked'])}\n"
            f"├ API failures: {DATA['stats'].get('api_fail', 0)}\n"
            f"├ Maintenance: {'ON' if CFG['maint'] else 'OFF'} · tracking {'PAUSED' if CFG['paused'] else 'running'}\n"
            f"└ Uptime: {uptime()}")


def apply_backup(raw: bytes):
    try:
        d = json.loads(raw.decode("utf-8"))
        if not isinstance(d, dict) or "cfg" not in d:
            return False, "That file is not a bot backup."
    except Exception:
        return False, "Couldn't read that file."
    CFG.update(d.get("cfg") or {})
    for k in DATA:
        if k in d and d[k] is not None:
            DATA[k] = d[k]
    if not isinstance(CFG.get("week"), list) or len(CFG["week"]) != 7:
        CFG["week"] = list(DEF_CFG["week"])
    return True, f"{len(DATA['users'])} users, {len(DATA['bans'])} bans, {len(DATA['premium'])} premium, {len((DATA.get('tracks') or {}))} tracked players."


def drop_tracks_of_user(user_id):
    for u in list(TRACKS):
        t = TRACKS[u]
        if user_id in t["subs"]:
            t["subs"].remove(user_id)
            if not t["subs"]:
                TRACKS.pop(u, None)


async def drop_uid(app_bot, uid, why_txt):
    t = TRACKS.pop(uid, None)
    if not t:
        return 0
    for c in t["subs"]:
        try:
            await app_bot.send_message(c, bq(f"<b>TRACKING STOPPED</b>\n\nUID {cp(uid)}\n{esc(why_txt)}"), parse_mode=ParseMode.HTML)
        except Exception:
            pass
    return len(t["subs"])


async def do_broadcast(bot, owner_chat, text, src=None):
    ids = [int(u) for u, r in DATA["users"].items() if r.get("dm") and int(u) not in DATA["bans"]]
    ok = bad = 0
    for u in ids:
        for attempt in range(2):
            try:
                if src is not None:
                    await bot.copy_message(u, src.chat.id, src.message_id)
                else:
                    try:
                        await bot.send_message(u, bq(text), parse_mode=ParseMode.HTML)
                    except Exception as e:
                        if isinstance(e, (Forbidden, RetryAfter)):
                            raise
                        await bot.send_message(u, bq(esc(re.sub(r"<[^>]+>", "", text))), parse_mode=ParseMode.HTML)
                ok += 1
                break
            except RetryAfter as e:
                await asyncio.sleep(min(float(getattr(e, "retry_after", 3)), 30))
            except Forbidden:
                (DATA["users"].get(str(u)) or {})["dm"] = False
                bad += 1
                break
            except Exception:
                bad += 1
                break
        await asyncio.sleep(0.06)
    STORE.touch()
    try:
        await bot.send_message(owner_chat, bq(f"<b>BROADCAST DONE</b>\n\n├ Sent: <b>{ok}</b>\n└ Failed: <b>{bad}</b>"), parse_mode=ParseMode.HTML)
    except Exception:
        pass


def _target_id(msg, a):
    for x in a:
        if re.fullmatch(r"-?\d{2,15}", x):
            return int(x)
    rm = getattr(msg, "reply_to_message", None)
    fu = getattr(rm, "from_user", None)
    return getattr(fu, "id", None)


async def owner_cmd(update, ctx, msg, cmd, arg):
    bot = ctx.bot
    arg = (arg or "").strip()
    a = arg.split()

    async def say(txt, kb=None):
        await rt(msg, txt, add=False, parse_mode=ParseMode.HTML, reply_markup=kb)

    if cmd in ("panel",):
        text, kb = panel_view()
        await say(text, kb)
    elif cmd == "admin":
        await say(admin_help())
    elif cmd == "stats":
        await say(stats_text())
    elif cmd == "maint":
        w = a[0].lower() if a else ""
        if w in ("on", "off"):
            CFG["maint"] = w == "on"
            if w == "on" and len(a) > 1:
                CFG["maint_msg"] = arg.split(None, 1)[1][:400]
            STORE.touch()
            await STORE.save()
        await say(f"<b>MAINTENANCE {'ON' if CFG['maint'] else 'OFF'}</b>\n\n"
                  + (f"Users see: {esc(CFG['maint_msg'])}\n\n" if CFG["maint"] else "")
                  + "<code>/maint on Back in 1 hour</code>\n<code>/maint off</code>")
    elif cmd == "trackpause":
        w = a[0].lower() if a else ""
        CFG["paused"] = (w == "on") if w in ("on", "off") else not CFG["paused"]
        STORE.touch()
        await STORE.save()
        await say(f"<b>LIVE TRACKING {'PAUSED' if CFG['paused'] else 'RUNNING'}</b>")
    elif cmd == "blockuid":
        if not a or not UID_RE.match(a[0]):
            await say("Usage: <code>/blockuid &lt;uid&gt; [reason]</code>")
            return
        DATA["blocked"][a[0]] = " ".join(a[1:])[:100]
        n = await drop_uid(bot, a[0], "This UID is no longer available.")
        PLAYER_CACHE.pop(a[0], None)
        STORE.touch()
        await STORE.save()
        if n:
            await tstore_save()
        await say(f"<b>UID BLOCKED</b>\n\n{cp(a[0])}\nSearch, quick commands and tracking are now refused."
                  + (f"\nStopped tracking for {n} watcher(s)." if n else ""))
    elif cmd == "unblockuid":
        if a and DATA["blocked"].pop(a[0], None) is not None:
            STORE.touch()
            await STORE.save()
            await say(f"<b>UID UNBLOCKED</b>\n\n{cp(a[0])}")
        else:
            await say("That UID isn't blocked. Usage: <code>/unblockuid &lt;uid&gt;</code>")
    elif cmd == "blocklist":
        b = DATA["blocked"]
        body = "\n".join(("└ " if i == len(b) - 1 else "├ ") + cp(u) + (f" — {esc(r)}" if r else "") for i, (u, r) in enumerate(b.items())) or "Nothing blocked."
        await say(f"<b>BLOCKED UIDS ({len(b)})</b>\n\n{body}")
    elif cmd == "ban":
        t = _target_id(msg, a)
        if not t or is_owner(t):
            await say("Usage: <code>/ban &lt;user id&gt;</code> or reply to the user's message.")
            return
        if t not in DATA["bans"]:
            DATA["bans"].append(t)
        drop_tracks_of_user(t)
        STORE.touch()
        await STORE.save()
        await tstore_save()
        await say(f"<b>USER BANNED</b>\n\n{cp(t)} · {esc(uname(t))}")
    elif cmd == "unban":
        t = _target_id(msg, a)
        if t in DATA["bans"]:
            DATA["bans"].remove(t)
            STORE.touch()
            await STORE.save()
            await say(f"<b>USER UNBANNED</b>\n\n{cp(t)}")
        else:
            await say("That user isn't banned.")
    elif cmd == "banlist":
        b = DATA["bans"]
        body = "\n".join(("└ " if i == len(b) - 1 else "├ ") + cp(u) + f" · {esc(uname(u))}" for i, u in enumerate(b)) or "Nobody is banned."
        await say(f"<b>BANNED USERS ({len(b)})</b>\n\n{body}")
    elif cmd == "limit":
        if not a:
            ov = CFG["limit_users"]
            body = "\n".join(f"├ {cp(u)} · {esc(uname(u))}: <b>{n}</b>" for u, n in ov.items()) or "No per-user overrides."
            await say(f"<b>TRACK LIMITS</b>\n\n├ Default per user: <b>{CFG['limit_default']}</b>\n├ Premium: <b>{CFG['limit_premium']}</b> for {CFG['premium_days']} days\n└ Total players: <b>{CFG['limit_total']}</b>\n\n{body}\n\n"
                      "<code>/limit 3</code> default · <code>/limit premium 5</code>\n<code>/limit &lt;user id&gt; 5</code> one user\n<code>/limit &lt;user id&gt; reset</code>\n<code>/limit total 60</code>")
        elif a[0].lower() == "premium" and len(a) > 1 and a[1].isdigit():
            CFG["limit_premium"] = int(a[1])
            STORE.touch(); await STORE.save()
            await say(f"<b>PREMIUM LIMIT</b> is now <b>{a[1]}</b> players.")
        elif a[0].lower() == "total" and len(a) > 1 and a[1].isdigit():
            CFG["limit_total"] = int(a[1])
            STORE.touch(); await STORE.save()
            await say(f"<b>TOTAL LIMIT</b> set to <b>{a[1]}</b> players.")
        elif len(a) == 1 and a[0].isdigit() and len(a[0]) < 5:
            CFG["limit_default"] = int(a[0])
            STORE.touch(); await STORE.save()
            await say(f"<b>DEFAULT LIMIT</b> is now <b>{a[0]}</b> players per user.")
        elif len(a) > 1 and re.fullmatch(r"\d{2,15}", a[0]):
            if a[1].lower() in ("reset", "default"):
                CFG["limit_users"].pop(a[0], None)
                txt = f"{cp(a[0])} back to the default (<b>{CFG['limit_default']}</b>)."
            elif a[1].isdigit():
                CFG["limit_users"][a[0]] = int(a[1])
                txt = f"{cp(a[0])} · {esc(uname(a[0]))} can now track <b>{a[1]}</b> players."
            else:
                await say("Usage: <code>/limit &lt;user id&gt; &lt;n|reset&gt;</code>")
                return
            STORE.touch(); await STORE.save()
            await say("<b>LIMIT UPDATED</b>\n\n" + txt)
        else:
            await say("Usage: <code>/limit 3</code> · <code>/limit &lt;user id&gt; 5</code> · <code>/limit total 60</code>")
    elif cmd in ("searchlimit", "alertlimit"):
        key, ukey, unit, what = (("search_daily", "search_users", "searches per day", "SEARCH LIMIT") if cmd == "searchlimit"
                                 else ("alert_daily", "alert_users", "alerts in any 24 hours", "ALERT LIMIT"))
        note = ""
        if a and a[0].isdigit() and len(a) == 1 and len(a[0]) < 6:
            CFG[key] = int(a[0])
            note = f"Default for everyone is now {CFG[key] or 'unlimited'}.\n\n"
        elif len(a) == 2 and re.fullmatch(r"\d{2,15}", a[0]) and (a[1].isdigit() or a[1].lower() in ("reset", "default")):
            if a[1].isdigit():
                CFG[ukey][a[0]] = int(a[1])
                note = f"{cp(a[0])} · {esc(uname(a[0]))} now gets <b>{int(a[1]) or 'unlimited'}</b> {unit}.\n\n"
            else:
                CFG[ukey].pop(a[0], None)
                note = f"{cp(a[0])} is back to the default.\n\n"
        elif a:
            await say(f"Usage: <code>/{cmd} 50</code> (everyone) · <code>/{cmd} &lt;user id&gt; 200</code> · <code>/{cmd} &lt;user id&gt; reset</code> · 0 = unlimited")
            return
        STORE.touch(); await STORE.save()
        ov = "\n".join(f"├ {cp(u)} · {esc(uname(u))}: <b>{n or 'unlimited'}</b>" for u, n in CFG[ukey].items()) or "No per-user overrides."
        await say(f"<b>{what}</b>\n\n{note}Default: <b>{CFG[key] or 'unlimited'}</b> {unit}\n\n{ov}")
    elif cmd == "trackspeed":
        if len(a) == 2 and all(re.fullmatch(r"\d+(\.\d+)?", x) for x in a):
            lo, hi = float(a[0]), float(a[1])
            if lo < 2 or hi < lo or hi > 600:
                await say("Use <code>/trackspeed &lt;min&gt; &lt;max&gt;</code> in seconds: min 2 or more, max up to 600. Example: <code>/trackspeed 5 10</code>")
                return
            CFG["track_min"], CFG["track_max"] = lo, hi
            STORE.touch(); await STORE.save()
        await say(f"<b>PROFILE CHECK SPEED</b>\n\nEvery player is checked at a random moment between <b>{tmin():g}</b> and <b>{tmax():g}</b> seconds.\n<code>/trackspeed 5 10</code> · <code>/trackspeed 8 15</code>\n\nOutfit, banner and avatar: <b>{oscan():g} s</b> (/outfitscan)")
    elif cmd == "outfitscan":
        if a and re.fullmatch(r"\d+(\.\d+)?", a[0]):
            v = float(a[0])
            if not 10 <= v <= 3600:
                await say("Use <code>/outfitscan &lt;seconds&gt;</code> between 10 and 3600. Example: <code>/outfitscan 120</code>")
                return
            CFG["outfit_scan"] = v
            STORE.touch(); await STORE.save()
        await say(f"<b>OUTFIT SCAN</b>\n\nOutfit, banner and avatar are checked every <b>{oscan():g} s</b> ({oscan() / 60:g} min).\n<code>/outfitscan 120</code>")
    elif cmd == "forcejoin":
        if a and a[0].lower() in ("off", "none", "no"):
            CFG["force_join"] = ""
        elif a and (a[0].startswith("@") or a[0].startswith("http")):
            CFG["force_join"] = a[0]
        STORE.touch(); await STORE.save()
        await say(f"<b>FORCE JOIN</b>\n\n{esc(CFG['force_join']) or 'Off'}\n<code>/forcejoin @channel</code> (make me an admin there) · <code>/forcejoin off</code>")
    elif cmd == "framecolor":
        w = [x.lower() for x in a]
        hx = [i for i, x in enumerate(w) if re.fullmatch(r"#?[0-9a-f]{6}", x) and x not in COLORS]
        if hx:  # hex code -> nearest of the 9 colours Telegram can show
            w[hx[0]] = nearest_color(w[hx[0]])
        if len(w) == 1 and (w[0] == "auto" or w[0] in COLORS):
            CFG["frame"] = w[0]
        elif len(w) == 2 and w[0] in DAYS and (w[1] in COLORS or w[1] == "auto"):
            CFG["week"][DAYS.index(w[0])] = "" if w[1] == "auto" else w[1]
            CFG["frame"] = "auto"
        elif w:
            await say("Colours: " + ", ".join(COLORS) + "\n<code>/framecolor auto</code> · <code>/framecolor blue</code> · <code>/framecolor mon red</code> · <code>/framecolor week red green blue ...</code> (7)")
            return
        STORE.touch(); await STORE.save()
        ov = ", ".join(f"{d} {c}" for d, c in zip(DAYS, CFG["week"]) if c) or "none"
        await say(f"<b>FRAME COLOUR</b>\n\nMode: <b>{esc(CFG['frame'])}</b> (auto = a new colour every day, all 9 in turn)\nToday: {frame_strip() or 'no strip'}\nWeekday overrides: {esc(ov)}\n\n<code>/framecolor auto</code> · <code>/framecolor red</code> (fixed) · <code>/framecolor ff69b4</code> (nearest colour)\n<code>/framecolor mon blue</code> · <code>/framecolor mon auto</code> (clear)")
    elif cmd == "framestrip":
        if a and a[0].isdigit() and 0 <= int(a[0]) <= 16:
            CFG["strip_len"] = int(a[0])
            STORE.touch(); await STORE.save()
        await say(f"<b>FRAME STRIP</b>\n\nLength: <b>{CFG['strip_len']}</b> {frame_strip()}\n<code>/framestrip 8</code> · <code>/framestrip 0</code> = no strip")
    elif cmd == "setwelcome":
        if arg.lower() == "reset":
            CFG["welcome"] = ""
        elif arg:
            CFG["welcome"] = arg[:900]
        else:
            await say("Usage: <code>/setwelcome Welcome {name}!</code> or <code>/setwelcome reset</code>\nFields: {name} {first} {mention} {id} {limit} {searches}")
            return
        STORE.touch(); await STORE.save()
        await rt(msg, welcome_caption(update.effective_user, ctx.bot.username), add=False, parse_mode=ParseMode.HTML)
    elif cmd == "welcome":
        await say("<b>WELCOME TEXT</b>\n\n<code>" + esc(CFG["welcome"] or DEFAULT_WELCOME) + "</code>")
    elif cmd in ("tracked", "user"):
        only = int(a[0]) if a and re.fullmatch(r"\d{2,15}", a[0]) else None
        who = {}
        for u, t in TRACKS.items():
            for c in t["subs"]:
                if only is None or c == only:
                    who.setdefault(c, []).append((u, t))
        if cmd == "user" and only is not None and only not in who:
            who[only] = []
        if not who:
            await say("<b>TRACKING</b>\n\nNobody is being tracked.")
            return
        secs = [f"<b>TRACKING BY USER</b>\n{len(who)} user(s) · stop one: /forcestop &lt;uid&gt;"]
        for c, items in who.items():
            pu = premium_until(c)
            head = f"<b>{esc(uname(c))}</b> · {cp(c)}"
            meta = [f"Tracking {len(items)} of {lim_txt(c)}" + (f" · premium until {datetime.fromtimestamp(pu, IST).strftime('%d %b %Y')}" if pu else "")]
            if only is not None:
                r = DATA["users"].get(str(c)) or {}
                meta.append(f"Searches: {r.get('s', 0)} · first seen {datetime.fromtimestamp(r['t'], IST).strftime('%d %b %Y') if r.get('t') else '—'}")
            if only is not None:
                meta.append(f"Limits: searches {search_limit_for(c) or 'unlimited'}/day · alerts {alert_limit_for(c) or 'unlimited'}/24h ({len(alerts_used(c))} used)")
            lines = [head] + [f"├ {x}" for x in meta]
            for i, (u, t) in enumerate(items):
                st = (t.get("sub_at") or {}).get(str(c)) or t.get("since")
                lines.append(("└ " if i == len(items) - 1 else "├ ") + f"{esc(clean(t.get('name')) or u)} · {cp(u)}\n│   Started: {esc(tss(st) if st else '—')} ({esc(ago(st))})\n│   Changes caught: {t.get('n', 0)}")
            secs.append("\n".join(lines))
        for part in pack(secs):
            await say(part)
    elif cmd == "ping":
        t0 = time.time()
        try:
            r = await http().get(INFO_API, params={"uid": "1"}, timeout=15)
            api_s = f"reachable (HTTP {r.status_code}, {int((time.time() - t0) * 1000)} ms)"
        except Exception as e:
            api_s = f"NOT reachable ({esc(why(e))})"
        t0 = time.time()
        try:
            r = await http().get(ITEM_API, params={"q": "ak"}, timeout=15)
            item_s = f"reachable (HTTP {r.status_code}, {int((time.time() - t0) * 1000)} ms)"
        except Exception as e:
            item_s = f"NOT reachable ({esc(why(e))})"
        try:
            dbk = str(db.backend())
        except Exception:
            dbk = "unknown"
        await say("<b>HEALTH</b>\n\n"
                  f"├ Info API: {api_s}\n├ Item API: {item_s}\n"
                  f"├ Tracking storage: {esc(dbk)}\n"
                  f"├ Settings backup: {'MongoDB + file' if STORE.col is not None else 'file only'}\n"
                  f"├ Images (Pillow): {'on' if PIL_OK else 'off'}\n"
                  f"├ Live tracking: {'PAUSED' if CFG['paused'] else 'running'} · {len(TRACKS)} players\n"
                  f"└ Uptime: {uptime()}")
    elif cmd == "backup":
        await STORE.save()
        try:
            data = json.dumps({"_ts": time.time(), "cfg": CFG, **DATA}, ensure_ascii=False, indent=1).encode("utf-8")
            await bot.send_document(msg.chat.id, document=data, filename=f"ffbot-backup-{today()}.json",
                                    caption="Backup of settings, users, bans, premium and tracking. To restore, reply to this file with /restore")
        except Exception as e:
            await say(f"Backup failed: {esc(why(e))}")
    elif cmd == "restore":
        doc = getattr(getattr(msg, "reply_to_message", None), "document", None)
        if not doc:
            await say("Reply to a backup file with <code>/restore</code>.")
            return
        try:
            f = await bot.get_file(doc.file_id)
            ok, info = apply_backup(bytes(await f.download_as_bytearray()))
        except Exception as e:
            await say(f"Restore failed: {esc(why(e))}")
            return
        if ok:
            STORE.touch()
            await STORE.save()
            await tstore_load()
        await say(f"<b>{'RESTORED' if ok else 'RESTORE FAILED'}</b>\n\n{esc(info)}")
    elif cmd == "newuseralert":
        if a and a[0].lower() in ("on", "off"):
            CFG["newuser_alert"] = a[0].lower() == "on"
            STORE.touch(); await STORE.save()
        await say(f"<b>NEW USER ALERT</b>\n\n{'ON' if CFG.get('newuser_alert') else 'OFF'} — you get a DM when someone uses the bot for the first time.\n<code>/newuseralert on</code> · <code>/newuseralert off</code>")
    elif cmd == "premium":
        t = _target_id(msg, a)
        days = next((int(x) for x in a[1:] if x.isdigit()), int(CFG["premium_days"])) if len(a) > 1 else int(CFG["premium_days"])
        if not t:
            await say(f"Usage: <code>/premium &lt;user id&gt; [days]</code> (default {CFG['premium_days']} days → track limit {CFG['limit_premium']}). Or reply to the user's message.")
            return
        start = max(premium_until(t), time.time())  # extends if already premium
        DATA["premium"][str(t)] = start + days * 86400
        DATA["premium_n"].pop(str(t), None)
        STORE.touch(); await STORE.save()
        until = datetime.fromtimestamp(DATA["premium"][str(t)], IST).strftime("%d %b %Y")
        try:
            await bot.send_message(t, bq(f"<b>PREMIUM ACTIVATED</b>\n\nYou can now track up to <b>{limit_for(t)}</b> players until <b>{until}</b>."), parse_mode=ParseMode.HTML)
        except Exception:
            pass
        await say(f"<b>PREMIUM GIVEN</b>\n\n{cp(t)} · {esc(uname(t))}\nTrack limit <b>{limit_for(t)}</b> until <b>{until}</b> ({days} days).")
    elif cmd == "unpremium":
        t = _target_id(msg, a)
        if t and DATA["premium"].pop(str(t), None) is not None:
            STORE.touch(); await STORE.save()
            await say(f"<b>PREMIUM REMOVED</b>\n\n{cp(t)} · {esc(uname(t))}")
        else:
            await say("Usage: <code>/unpremium &lt;user id&gt;</code> (that user has no premium)")
    elif cmd == "premiumlist":
        rows = [(u, e) for u, e in DATA["premium"].items() if e > time.time()]
        body = "\n".join(("└ " if i == len(rows) - 1 else "├ ") + f"{cp(u)} · {esc(uname(u))} · until {datetime.fromtimestamp(e, IST).strftime('%d %b %Y')}" for i, (u, e) in enumerate(sorted(rows, key=lambda r: r[1]))) or "Nobody has premium."
        await say(f"<b>PREMIUM USERS ({len(rows)})</b>\n\n{body}")
    elif cmd == "forcestop":
        if a and a[0] in TRACKS:
            n = await drop_uid(bot, a[0], "Stopped by the admin.")
            await tstore_save()
            await say(f"<b>STOPPED</b>\n\n{cp(a[0])} · {n} watcher(s) notified.")
        else:
            await say("Usage: <code>/forcestop &lt;uid&gt;</code> (see /tracked)")
    elif cmd == "broadcast":
        src = getattr(msg, "reply_to_message", None)
        if not arg and not src:
            await say("Usage: <code>/broadcast your text</code> or reply to a message with /broadcast.")
            return
        n = sum(1 for r in DATA["users"].values() if r.get("dm"))
        task = asyncio.create_task(do_broadcast(bot, msg.chat.id, arg, src if not arg else None))
        _TASKS.add(task)
        task.add_done_callback(_TASKS.discard)
        await say(f"<b>BROADCAST STARTED</b>\n\nSending to {n} users. I'll tell you when it's done.")


async def owner_cb(q, val):
    user = q.from_user.id
    if not is_owner(user):
        await q.answer("Owner only.", show_alert=True)
        return
    if val == "maint":
        CFG["maint"] = not CFG["maint"]
    elif val == "pause":
        CFG["paused"] = not CFG["paused"]
    elif val == "frame":
        modes = ["auto"] + list(COLORS)
        CFG["frame"] = modes[(modes.index(CFG["frame"]) + 1) % len(modes)] if CFG["frame"] in modes else "auto"
    elif val == "strip":
        steps = [0, 4, 8, 12, 16]
        CFG["strip_len"] = steps[(steps.index(CFG["strip_len"]) + 1) % len(steps)] if CFG["strip_len"] in steps else 8
    elif val == "stats":
        await q.answer()
        await q.message.reply_text(bq(stats_text()), parse_mode=ParseMode.HTML)
        return
    STORE.touch()
    await q.answer("Saved")
    text, kb = panel_view()
    try:
        await q.message.edit_text(bq(text), parse_mode=ParseMode.HTML, reply_markup=kb)
    except Exception as e:
        log.info("panel edit skipped: %r", e)


# ───────────────────────── main ─────────────────────────
def keep_alive():
    port = os.getenv("PORT")
    if not port:
        return

    class H(BaseHTTPRequestHandler):
        def do_GET(self):
            self.send_response(200)
            self.end_headers()
            self.wfile.write(b"ok")

        def log_message(self, *a):
            pass

    threading.Thread(target=HTTPServer(("0.0.0.0", int(port)), H).serve_forever, daemon=True).start()


COMMANDS = [
    ("start", "Welcome"),
    ("help", "All commands & how to use"),
    ("info", "Full player profile: /info <uid>"),
    ("level", "Level, EXP & likes"),
    ("bio", "Player bio"),
    ("outfit", "Equipped outfit & weapon skins"),
    ("rank", "BR & CS rank"),
    ("login", "Created & last login"),
    ("clan", "Guild details"),
    ("leader", "Guild leader details"),
    ("pet", "Pet details"),
    ("item", "Item lookup: /item <id or name>"),
    ("track", "Live profile alerts (private chat only)"),
    ("tracklist", "Players you are tracking"),
    ("untrack", "Stop tracking"),
    ("quiet", "Mute tracking alerts at night"),
    ("history", "Your last searches"),
    ("plan", "Your limits"),
]
OWNER_COMMANDS = [
    ("panel", "Owner panel"), ("admin", "All owner commands"), ("stats", "Bot stats"),
    ("maint", "Maintenance mode on/off"), ("blockuid", "Block a UID"), ("unblockuid", "Unblock a UID"),
    ("ban", "Ban a user"), ("unban", "Unban a user"), ("limit", "Track limits"), ("broadcast", "Message all users"),
    ("tracked", "Who tracks whom"), ("premium", "Give premium"), ("backup", "Backup everything"), ("ping", "Health check"), ("alertlimit", "Alert limit"), ("trackspeed", "Check speed"), ("outfitscan", "Outfit scan time"), ("framecolor", "Frame colour"), ("setwelcome", "Edit welcome message"),
]


async def post_init(app):
    global BOT_USER
    BOT_USER = app.bot.username or ""
    await STORE.load()
    await tstore_load()
    app.bot_data["track_task"] = asyncio.create_task(track_loop(app))
    app.bot_data["store_task"] = asyncio.create_task(store_loop())
    app.bot_data["premium_task"] = asyncio.create_task(premium_loop(app))
    try:
        await app.bot.set_my_commands([BotCommand(c, d) for c, d in COMMANDS])
        from telegram import BotCommandScopeChat  # the owner also sees the admin commands in their menu

        await app.bot.set_my_commands([BotCommand(c, d) for c, d in COMMANDS + OWNER_COMMANDS], scope=BotCommandScopeChat(OWNER_ID))
    except Exception as e:
        log.warning("set_my_commands failed: %r", e)


async def on_error(update, ctx):
    log.warning("handler error: %r", ctx.error)
    e = ctx.error
    if type(e).__name__ not in ("TimedOut", "NetworkError", "RetryAfter"):
        await owner_alert(ctx.bot, f"<code>{esc(repr(e)[:300])}</code>", key=type(e).__name__)


def main():
    if not BOT_TOKEN:
        raise SystemExit("Set the BOT_TOKEN environment variable.")
    if not PIL_OK:
        log.warning("Pillow not installed - image cards disabled (pip install Pillow)")
    ensure_font()
    keep_alive()
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .concurrent_updates(True)
        .connect_timeout(20)
        .read_timeout(30)
        .write_timeout(30)
        .pool_timeout(20)
        .post_init(post_init)
        .build()
    )
    app.add_error_handler(on_error)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_cmd))
    app.add_handler(CallbackQueryHandler(on_cb))
    app.add_handler(MessageHandler(filters.TEXT, router))
    log.info("Bot started")
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()
