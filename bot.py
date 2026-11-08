"""
Free Fire Info Bot (Telegram)
  /info <uid>  |  info <uid>  |  /get <uid>  |  get <uid>  |  uid <uid>
  /item <item id or name>

Every value is wrapped in <code> so a single tap copies it.
Single file: missing packages are installed automatically on first run.
Env vars: BOT_TOKEN (required), INFO_API, ITEM_API, WATERMARK, FONT_PATH, PORT (Render keep-alive)
"""
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
from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, Update
from telegram.constants import ChatAction, ParseMode
from telegram.error import TimedOut
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
MAX_LEN = 3900       # Telegram limit is 4096
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
    return (fx(label), "Yes ✅" if value else "No ❌")


def E(label, value):
    return (fx(label), "Equipped ✅" if value else "Not Equipped ❌")


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
        R("Privacy", ("🔒 " if "CLOSED" in str(privacy) else "🔓 ") + enum_txt(privacy, "PRIVACY_")),
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
        f"<b>{fx('🍁 Player Profile Info')}</b>",
        section("👤 Basic", basic),
        section("✅ Account", acc),
        section("💬 Social", social),
        section("🐾 Pet", petrows),
        section("🏆 Rank", rank),
        section("🎒 Loadout", load),
        section("🛡 Guild", guild),
        f"⏱ {esc(js.get('Time_Spne', ''))} · {esc(WATERMARK)}",
    ]


# ───────────────────────── handlers ─────────────────────────
def welcome_caption():
    return (
        f"🍁 <b>{fx('Free Fire Player Info')}</b>\n"
        "Full profile, loadout &amp; item details from just a UID.\n\n"
        f"✨ <b>{fx('What you get')}</b>\n"
        "• Profile banner + loadout card\n"
        "• Rank, guild, pet, Honor Score &amp; Booyah Pass\n"
        "• Item names with pictures\n\n"
        f"🚀 <b>{fx('Try it')}</b>\n"
        "/info 6118588149\n"
        "/item 907102815\n\n"
        "📖 All commands: /help\n"
        "<i>Tap any value in the results to copy it. Works in groups too.</i>"
    )


def help_text():
    return (
        f"🍁 <b>{fx('Command Guide')}</b>\n"
        "Send a command followed by a player UID.\n\n"
        f"👤 <b>{fx('Player')}</b>\n"
        "/info &lt;uid&gt; — full profile with banner &amp; loadout card\n"
        "/level &lt;uid&gt; — level, EXP, likes &amp; prime level\n"
        "/bio &lt;uid&gt; — signature / bio text\n"
        "/outfit &lt;uid&gt; — equipped items &amp; weapon skins\n"
        "/rank &lt;uid&gt; — BR &amp; CS rank with points\n"
        "/login &lt;uid&gt; — account created &amp; last login\n\n"
        f"🛡 <b>{fx('Guild')}</b>\n"
        "/clan &lt;uid&gt; — guild name, level &amp; members\n"
        "/leader &lt;uid&gt; — guild leader's details\n\n"
        f"🐾 <b>{fx('Pet')}</b>\n"
        "/pet &lt;uid&gt; — pet name, level, skin &amp; skill\n\n"
        f"🧾 <b>{fx('Items')}</b>\n"
        "/item &lt;id&gt; — item details with picture\n"
        "/item &lt;name&gt; — search items by name\n\n"
        f"💡 <b>{fx('Tips')}</b>\n"
        "• Example: /info 6118588149\n"
        "• Without a slash also works: info 6118588149\n"
        "• Tap any value in the results to copy it\n"
        "• Works in groups: /info@botusername 6118588149"
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
        await msg.reply_text(
            part,
            parse_mode=ParseMode.HTML,
            reply_markup=kb if i == len(parts) - 1 else None,
        )


async def send_photo(msg, photo, text) -> bool:
    """Send photo (+ text as caption, or as a follow-up if too long).
    Returns True when the photo is out or MAY be out (timeout) so the caller must never
    send the same text again; False only when Telegram clearly rejected the photo."""
    cap = text if len(text) <= 1024 else None
    try:
        if cap:
            await msg.reply_photo(photo, caption=cap, parse_mode=ParseMode.HTML, **TO)
        else:
            await msg.reply_photo(photo, **TO)
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
            await msg.reply_photo(cards[0], **TO)
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
            await msg.reply_photo(c, **TO)
        except Exception as e:
            log.warning("card send failed: %r", e)


async def build_cards_safe(js, nm):
    try:
        return await asyncio.wait_for(build_cards(js, nm), timeout=40)
    except Exception as e:
        log.warning("cards failed: %r", e)
        return []


async def handle_info(msg, uid, force=False):
    await action(msg, ChatAction.TYPING)
    try:
        js = await fetch_player(uid, force)
    except Exception as e:
        log.warning("player fetch failed %s: %r", uid, e)
        await msg.reply_text(f"❌ Couldn't fetch this player ({why(e)}). Check the UID and try again.")
        return
    nm = await resolve_names(collect_ids(js))
    # images are rendered in the background while the details go out first
    cards_task = asyncio.create_task(build_cards_safe(js, nm)) if PIL_OK else None
    row = [InlineKeyboardButton("🔄 Refresh", callback_data=f"r:{uid}")]
    lead_id = (js.get("clan_basic_info") or {}).get("captain_id")
    if lead_id and str(lead_id) != str(uid):
        row.append(InlineKeyboardButton("👑 Leader", callback_data=f"c:{lead_id}"))
    try:
        await send_parts(msg, pack(build_player(js, nm)), InlineKeyboardMarkup([row]))
    except Exception as e:
        log.warning("details send failed: %r", e)
        if cards_task:
            cards_task.cancel()
        try:
            await msg.reply_text("❌ Couldn't send the info. Please try again.")
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
    return section("🧾 Item Info", rows)


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
            await msg.reply_text(f"❌ Item search is unavailable right now ({why(e)}).")
            return
    if not is_id:
        if not results:
            await msg.reply_text("❌ No items found.")
            return
        if len(results) > 1:
            lines = [f"{cp(x['id'])} → {esc(x['name'])}" for x in results[:15]]
            await msg.reply_text(
                f"🔎 <b>{len(results)} {fx('results')}</b>\n" + "\n".join(lines) + "\n\n<code>/item &lt;id&gt;</code>",
                parse_mode=ParseMode.HTML,
            )
            return
    iid = it["id"] if it else arg
    icon = await fetch_icon(iid)
    if not it and not icon:
        await msg.reply_text("❌ Item not found.")
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
        title = "📈 Level"
        rows = [R("Level", b.get("level")), R("EXP", b.get("exp"), fmt=indian),
                R("Likes", b.get("liked"), fmt=indian), R("Prime Level", (b.get("prime_info") or {}).get("prime_level"))]
    elif kind == "bio":
        title = "💬 Bio"
        bio = so.get("social_highlight", "")
        rows = [R("Bio", bio)]
        if clean(bio) != bio:
            rows.append(R("Bio (clean)", clean(bio)))
    elif kind == "outfit":
        title = "🎒 Outfit"
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
        title = "🏆 Rank"
        rows = [
            R("BR Rank", b.get("rank"), br_rank(b.get("rank"))),
            R("BR Points", b.get("ranking_points")),
            R("BR Max Rank", b.get("max_rank"), br_rank(b.get("max_rank"))),
            R("CS Rank", b.get("cs_rank")), R("CS Points", b.get("cs_ranking_points")),
            R("CS Max Rank", b.get("cs_max_rank")),
        ]
    elif kind == "pet":
        title = "🐾 Pet"
        rows = [
            R("Pet Name", pet.get("pet_name")), R("Pet Level", pet.get("level")), R("Pet EXP", pet.get("exp")),
            R("Skin ID", pet.get("skin_id"), n(pet.get("skin_id"))),
            R("Skill ID", pet.get("selected_skill_id"), n(pet.get("selected_skill_id"))),
        ]
    elif kind == "login":
        title = "🕒 Activity"
        rows = [R("Created", b.get("create_at"), fmt=ts), R("Last Login", b.get("last_login_at"), fmt=ts),
                R("Version", b.get("release_version"))]
    elif kind == "leader":
        title = "👑 Leader"
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
        title = "🛡 Guild"
        head = []
        rows = [
            R("Name", cl.get("clan_name")), R("Guild ID", cl.get("clan_id")),
            R("Level", cl.get("clan_level")),
            R("Members", f"{cl.get('current_members', 0)}/{cl.get('max_members', 0)}"),
            R("Leader ID", cl.get("captain_id")), R("Leader Name", ld.get("nickname")),
        ]
    return [section(title, head + rows)]


async def handle_quick(msg, kind, uid):
    await action(msg, ChatAction.TYPING)
    try:
        js = await fetch_player(uid)
    except Exception as e:
        log.warning("quick fetch failed %s: %r", uid, e)
        await msg.reply_text(f"❌ Couldn't fetch this player ({why(e)}). Check the UID and try again.")
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
    m = INFO_RE.match(text)
    if m:
        if limited(uid):
            await msg.reply_text("⏳ Slow down a little.")
            return
        await handle_info(msg, m.group(1))
        return
    m = QUICK_RE.match(text)
    if m:
        if limited(uid):
            await msg.reply_text("⏳ Slow down a little.")
            return
        await handle_quick(msg, m.group("c").lower(), m.group("u"))
        return
    m = ITEM_RE.match(text)
    if m and (m.group("a").isdigit() or m.group("p")):
        if limited(uid):
            await msg.reply_text("⏳ Slow down a little.")
            return
        await handle_item(msg, m.group("a"))
        return
    m = BARE_RE.match(text)
    if m:
        if m.group("c").lower() == "item":
            await msg.reply_text("Usage: /item <id or name>")
        else:
            await msg.reply_text(f"Usage: /{m.group('c').lower()} <uid>")


async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not msg or duplicate(update):
        return
    cap = welcome_caption()
    if PIL_OK:
        try:
            card = await asyncio.to_thread(render_welcome)
        except Exception as e:
            log.warning("welcome card failed: %r", e)
            card = None
        if card and await send_photo(msg, card, cap):
            return
    await msg.reply_text(cap, parse_mode=ParseMode.HTML)


async def help_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not msg or duplicate(update):
        return
    await msg.reply_text(help_text(), parse_mode=ParseMode.HTML)


async def on_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not q or not q.data or not q.message:
        return
    if duplicate(update):
        return
    if limited(q.from_user.id):
        await q.answer("⏳ Slow down a little.")
        return
    await q.answer()
    kind, _, val = q.data.partition(":")
    if kind == "r":
        await handle_info(q.message, val, force=True)
    elif kind == "c":
        await handle_info(q.message, val)


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
]


async def post_init(app):
    try:
        await app.bot.set_my_commands([BotCommand(c, d) for c, d in COMMANDS])
    except Exception as e:
        log.warning("set_my_commands failed: %r", e)


async def on_error(update, ctx):
    log.warning("handler error: %r", ctx.error)


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
