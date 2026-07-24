import asyncio
import hashlib
import html
import json
import os
import re
import sys
import time
import unicodedata
from collections import Counter
from datetime import datetime
from pathlib import Path
from typing import Any
from urllib.parse import parse_qs, quote, unquote, urljoin, urlparse
from zoneinfo import ZoneInfo

from playwright.async_api import BrowserContext, Page, Route, async_playwright


# =========================
# CẤU HÌNH
# =========================
TARGET_URL = "https://live03.chuoichientv.me/"
PLAYER_ORIGIN_FALLBACK = "https://live.chuoichien.tv"
OUTPUT_M3U = "chuoichien_live.m3u"
OUTPUT_PIPE_M3U = "chuoichien_live_pipe.m3u"
OUTPUT_VLC_M3U = "chuoichien_live_vlc.m3u"
OUTPUT_DEBUG = "chuoichien_debug.json"
OUTPUT_HOME_DEBUG_HTML = "chuoichien_home_debug.html"
OUTPUT_HOME_DEBUG_PNG = "chuoichien_home_debug.png"
SCANNER_VERSION = "3.4-UNIVERSAL-RAW-URL-HEADERS"


def read_env_bool(name: str, default: bool = True) -> bool:
    raw = os.getenv(name, "").strip().lower()
    if not raw:
        return default
    if raw in {"1", "true", "yes", "on"}:
        return True
    if raw in {"0", "false", "no", "off"}:
        return False
    print(f"⚠️ {name}={raw!r} không hợp lệ; dùng mặc định {default}.")
    return default


def read_env_int(name: str, default: int, minimum: int, maximum: int) -> int:
    raw = os.getenv(name, "").strip()
    if not raw:
        return default
    try:
        value = int(raw)
    except ValueError:
        print(f"⚠️ {name}={raw!r} không hợp lệ; dùng mặc định {default}.")
        return default
    return max(minimum, min(value, maximum))


CONCURRENCY_LIMIT = read_env_int(
    "SOCOLIVE_MATCH_CONCURRENCY", 4, minimum=1, maximum=12
)
HOME_WAIT_MS = read_env_int(
    "SOCOLIVE_HOME_WAIT_MS", 6000, minimum=1000, maximum=30000
)
STREAM_WAIT_SECONDS = read_env_int(
    "SOCOLIVE_ROOM_WAIT_SECONDS", 20, minimum=5, maximum=120
)
EXTRA_WAIT_AFTER_FIRST_STREAM = 5.0
FULL_SCAN = read_env_bool("SOCOLIVE_FULL_SCAN", True)
HEADLESS = True

# Dùng đúng User-Agent đã được kiểm chứng phát được bằng VLC.
UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/120.0.0.0 Safari/537.36"
)

STREAM_EXTENSIONS = (".m3u8", ".flv")
AD_MARKERS = (
    "doubleclick.",
    "googleads.",
    "/ads/",
    "/advert",
    "imasdk",
)

PLAY_SELECTORS = (
    ".vjs-big-play-button",
    ".plyr__control--overlaid",
    ".jw-icon-display",
    ".jw-display-icon-container",
    ".play-button",
    ".btn-play",
    "button[aria-label*='Play' i]",
    "button[title*='Play' i]",
    "[class*='play'][role='button']",
)

TIME_RE = re.compile(r"(?<!\d)([01]?\d|2[0-3])[:h.]([0-5]\d)(?!\d)", re.I)

SPORT_GROUP_ORDER = (
    "Bóng đá",
    "Bóng rổ",
    "Bóng chuyền",
    "Tennis",
    "Esports",
    "Khác",
)
SPORT_GROUP_RANK = {name: index for index, name in enumerate(SPORT_GROUP_ORDER)}
SPORT_KEYWORDS: dict[str, tuple[tuple[str, int], ...]] = {
    "Esports": (
        ("esports", 12), ("e sports", 12), ("esport", 12),
        ("counter strike", 9), ("cs2", 9), ("csgo", 9),
        ("dota", 9), ("league of legends", 9), ("valorant", 9),
        ("pubg", 8), ("mobile legends", 8), ("lien quan", 8),
        ("efootball", 8), ("fifa online", 8), ("arena of valor", 8),
    ),
    "Tennis": (
        ("tennis", 12), ("quan vot", 12), ("atp", 8), ("wta", 8),
        ("challenger", 7), ("wimbledon", 8), ("roland garros", 8),
        ("australian open", 8), ("us open", 7), ("davis cup", 7),
    ),
    "Bóng rổ": (
        ("bong ro", 12), ("basketball", 12), ("nba", 9), ("wnba", 9),
        ("euroleague", 8), ("fiba", 8), ("ncaa", 7), ("vba", 7),
        ("cba", 6), ("basket", 6),
    ),
    "Bóng chuyền": (
        ("bong chuyen", 12), ("volleyball", 12), ("fivb", 9),
        ("volleyball nations league", 10), ("nations league women", 8),
        ("nations league men", 8), ("vnl", 8), ("pvl", 7),
        ("cev", 5),
    ),
    "Bóng đá": (
        ("bong da", 12), ("football", 11), ("soccer", 11),
        ("futsal", 10), ("premier league", 8), ("champions league", 8),
        ("europa league", 8), ("conference league", 8),
        ("world cup", 7), ("asian cup", 7), ("copa", 6),
        ("uefa", 6), ("afc", 5), ("fc ", 4), (" fc", 4),
    ),
    "Khác": (
        ("cau long", 12), ("badminton", 12), ("bong ban", 12),
        ("table tennis", 12), ("baseball", 10), ("ice hockey", 10),
        ("hockey", 8), ("handball", 9), ("boxing", 9), ("mma", 9),
        ("motogp", 9), ("formula 1", 9), ("f1 racing", 9),
    ),
}


def normalize_search_text(value: str) -> str:
    text = unicodedata.normalize("NFKD", clean_text(value).lower())
    text = "".join(ch for ch in text if not unicodedata.combining(ch))
    text = re.sub(r"[^a-z0-9]+", " ", text)
    return f" {clean_text(text)} "


def classify_sport(*values: str, default: str = "Bóng đá") -> str:
    """Phân loại theo tín hiệu gần card/trang trận; tín hiệu đầu tiên có độ tin cậy cao thắng."""
    for value in values:
        normalized = normalize_search_text(value)
        if not normalized.strip():
            continue
        scores: dict[str, int] = {}
        for group, keywords in SPORT_KEYWORDS.items():
            score = 0
            for keyword, weight in keywords:
                token = f" {keyword.strip()} "
                if token in normalized or (len(keyword.strip()) >= 6 and keyword.strip() in normalized):
                    score += weight
            if score:
                scores[group] = score
        if not scores:
            continue
        ranked = sorted(scores.items(), key=lambda item: item[1], reverse=True)
        if len(ranked) == 1 or ranked[0][1] > ranked[1][1]:
            return ranked[0][0]
    return default if default in SPORT_GROUP_RANK else "Khác"


def channel_id_for(result: dict[str, Any], stream_url: str, index: int) -> str:
    path_match = re.search(r"/live/(\d+)", result.get("url", ""))
    base = path_match.group(1) if path_match else hashlib.sha1(
        (result.get("url", "") + stream_url).encode("utf-8")
    ).hexdigest()[:12]
    return f"chuoichien-{base}-{index}"


def clean_text(value: str) -> str:
    return re.sub(r"\s+", " ", value or "").strip()


def decode_url_repeatedly(value: str, rounds: int = 3) -> str:
    current = html.unescape(value or "").replace("\\/", "/").strip()
    for _ in range(rounds):
        decoded = unquote(current)
        if decoded == current:
            break
        current = decoded
    return current.strip()


def absolute_url(value: str, base: str = TARGET_URL) -> str:
    value = decode_url_repeatedly(value)
    if not value or value.startswith(("data:", "blob:", "javascript:")):
        return ""
    try:
        return urljoin(base, value)
    except Exception:
        return value


def origin_from_url(value: str) -> str:
    try:
        parsed = urlparse(value)
        if parsed.scheme and parsed.netloc:
            return f"{parsed.scheme}://{parsed.netloc}"
    except Exception:
        pass
    return ""


def extract_time(value: str) -> str:
    text = clean_text(value)

    # JSON/JSON-LD thường trả ISO UTC. Chuyển đúng sang giờ Việt Nam trước.
    iso_match = re.search(
        r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}(?::\d{2}(?:\.\d+)?)?(?:Z|[+-]\d{2}:?\d{2})?",
        text,
    )
    if iso_match:
        try:
            iso_value = iso_match.group(0).replace("Z", "+00:00")
            parsed = datetime.fromisoformat(iso_value)
            if parsed.tzinfo is not None:
                parsed = parsed.astimezone(ZoneInfo("Asia/Ho_Chi_Minh"))
            return parsed.strftime("%H:%M")
        except Exception:
            pass

    match = TIME_RE.search(text)
    if not match:
        return ""
    return f"{int(match.group(1)):02d}:{match.group(2)}"


def stream_kind(url: str, content_type: str = "") -> str:
    clean = decode_url_repeatedly(url)
    lower_path = urlparse(clean).path.lower()
    lower_type = (content_type or "").lower()

    if ".m3u8" in lower_path or any(marker in lower_type for marker in (
        "application/vnd.apple.mpegurl", "application/x-mpegurl",
        "audio/mpegurl", "audio/x-mpegurl",
    )):
        return "m3u8"
    if ".flv" in lower_path or any(marker in lower_type for marker in (
        "video/x-flv", "video/flv", "application/x-flv",
    )):
        return "flv"
    return ""


def is_direct_stream_url(url: str, content_type: str = "") -> bool:
    if not url:
        return False
    clean = decode_url_repeatedly(url)
    parsed = urlparse(clean)
    lower_url = clean.lower()
    if parsed.scheme not in {"http", "https"}:
        return False
    if not stream_kind(clean, content_type):
        return False
    return not any(marker in lower_url for marker in AD_MARKERS)


def extract_stream_urls(raw_url: str, content_type: str = "") -> list[str]:
    """Tách luồng trực tiếp, kể cả streamUrl đã percent-encode trong iframe embed."""
    if not raw_url:
        return []

    pending = [raw_url]
    seen_values: set[str] = set()
    found: list[str] = []
    nested_param_names = {
        "streamurl", "stream_url", "stream", "url", "src", "file",
        "source", "video", "hls", "flv", "playurl", "play_url",
    }

    while pending and len(seen_values) < 60:
        value = decode_url_repeatedly(pending.pop(0))
        if not value or value in seen_values:
            continue
        seen_values.add(value)

        direct_type = content_type if value == decode_url_repeatedly(raw_url) else ""
        if is_direct_stream_url(value, direct_type):
            if value not in found:
                found.append(value)
            continue

        try:
            query = parse_qs(urlparse(value).query, keep_blank_values=False)
        except Exception:
            query = {}

        for key, values in query.items():
            if key.lower() not in nested_param_names:
                continue
            for nested in values:
                decoded = decode_url_repeatedly(nested)
                if decoded.startswith(("http://", "https://")):
                    pending.append(decoded)

        for match in re.findall(
            r"https?://[^\s\"'<>]+?(?:\.m3u8|\.flv)(?:\?[^\s\"'<>]*)?",
            decode_url_repeatedly(value),
            flags=re.IGNORECASE,
        ):
            pending.append(match.rstrip("),];"))

    return found


def stream_referer_hint(raw_candidate: str, frame_url: str = "") -> str:
    """Ưu tiên origin của iframe embed chứa streamUrl, không dùng nhầm trang trận."""
    decoded = decode_url_repeatedly(raw_candidate)
    if extract_stream_urls(decoded) and not is_direct_stream_url(decoded):
        embedded_origin = origin_from_url(decoded)
        if embedded_origin:
            return embedded_origin + "/"
    if frame_url:
        frame_origin = origin_from_url(frame_url)
        if frame_origin:
            return frame_origin + "/"
    return ""


def normalize_playback_referer(value: str) -> str:
    """Chuẩn hóa Referer cho player; ưu tiên root live.chuoichien.tv đã kiểm chứng."""
    candidate = decode_url_repeatedly(value)
    parsed = urlparse(candidate)
    if parsed.scheme and parsed.netloc:
        origin = f"{parsed.scheme}://{parsed.netloc}"
        if parsed.netloc.lower() == urlparse(PLAYER_ORIGIN_FALLBACK).netloc.lower():
            return origin + "/"
        return candidate
    return PLAYER_ORIGIN_FALLBACK + "/"


def clean_match_name(value: str, fallback_url: str) -> str:
    text = clean_text(value)
    # Ưu tiên dòng/đoạn chứa "vs" nếu card còn kèm giải, thời gian, trạng thái.
    pieces = [clean_text(p) for p in re.split(r"[\n|]", value or "") if clean_text(p)]
    vs_piece = next((p for p in pieces if re.search(r"\bvs\b", p, re.I)), "")
    if vs_piece:
        text = vs_piece

    text = TIME_RE.sub(" ", text)
    text = re.sub(
        r"(?i)\b(xem ngay|trực tiếp|hot|live|bóng đá|sắp diễn ra|đang diễn ra|socolive)\b",
        " ",
        text,
    )
    text = clean_text(text).strip(" -|•")

    if not re.search(r"\bvs\b", text, re.I):
        slug = unquote(urlparse(fallback_url).path.rstrip("/").split("/")[-1])
        slug = re.sub(r"-\d{2}-\d{2}-\d{4}-\d{4}$", "", slug)
        slug = re.sub(r"-vs-", " vs ", slug, flags=re.I)
        slug = slug.replace("-", " ")
        text = clean_text(slug)

    return text or fallback_url


def derive_match_info(
    url: str,
    raw_title: str = "",
    raw_time: str = "",
) -> tuple[str, str, str]:
    parsed = urlparse(url)
    query = parse_qs(parsed.query)
    match_name = clean_match_name(raw_title, url)
    time_str = extract_time(raw_time) or extract_time(raw_title)

    if not time_str:
        suffix = re.search(r"-(\d{2})(\d{2})/?$", parsed.path)
        if suffix:
            time_str = f"{suffix.group(1)}:{suffix.group(2)}"

    blv_name = ""
    if "blv" in query and raw_title and not re.search(r"\bvs\b", raw_title, re.I):
        blv_name = clean_text(raw_title)

    return match_name, time_str, blv_name


def is_good_logo_url(value: str) -> bool:
    lower = (value or "").lower()
    if not value or value.startswith(("data:", "blob:")):
        return False
    bad = ("avatar", "banner", "advert", "doubleclick", "googleads", "emoji", "flag")
    return not any(marker in lower for marker in bad)


def choose_logo(candidates: list[str], base: str) -> str:
    seen: set[str] = set()
    for value in candidates:
        fixed = absolute_url(value, base)
        if fixed and fixed not in seen and is_good_logo_url(fixed):
            seen.add(fixed)
            return fixed
    return ""


async def install_route_filter(page: Page, homepage: bool = False) -> None:
    """Cho ảnh tải để lazy-load logo hoạt động; chỉ chặn font và media ở trang chủ."""
    blocked_types = {"font"}
    if homepage:
        blocked_types.add("media")

    async def route_handler(route: Route) -> None:
        if route.request.resource_type in blocked_types:
            await route.abort()
        else:
            await route.continue_()

    await page.route("**/*", route_handler)


async def collect_dom_stream_candidates(page: Page) -> list[dict[str, str]]:
    candidates: list[dict[str, str]] = []
    seen: set[tuple[str, str]] = set()

    for frame in page.frames:
        try:
            frame_candidates = await frame.evaluate(
                r"""() => {
                    const out = new Set();
                    try {
                        for (const entry of performance.getEntriesByType("resource")) {
                            if (entry && entry.name) out.add(entry.name);
                        }
                    } catch (_) {}

                    document.querySelectorAll(
                        "video, source, iframe, embed, object, " +
                        "[data-stream], [data-stream-url], [data-url], [data-src]"
                    ).forEach((el) => {
                        [
                            el.src, el.currentSrc, el.data,
                            el.getAttribute("src"), el.getAttribute("data"),
                            el.getAttribute("data-src"), el.getAttribute("data-url"),
                            el.getAttribute("data-stream"), el.getAttribute("data-stream-url"),
                            el.getAttribute("data-file")
                        ].forEach((value) => { if (value) out.add(value); });
                    });

                    const htmlText = document.documentElement
                        ? document.documentElement.innerHTML : "";
                    const normalized = htmlText.replace(/\\\//g, "/").replace(/&amp;/g, "&");
                    (normalized.match(
                        /https?:\/\/[^"' <>\n\r]+?(?:\.m3u8|\.flv)(?:\?[^"' <>\n\r]*)?/gi
                    ) || []).forEach((value) => out.add(value));
                    (normalized.match(
                        /https?:\/\/[^"' <>\n\r]+?(?:streamUrl|stream_url|file|src|url)=[^"' <>\n\r]+/gi
                    ) || []).forEach((value) => out.add(value));
                    return Array.from(out);
                }"""
            )
            for item in frame_candidates:
                key = (str(item), frame.url or "")
                if item and key not in seen:
                    seen.add(key)
                    candidates.append({"url": str(item), "frame_url": frame.url or ""})
        except Exception:
            continue

    return candidates


async def stimulate_player(page: Page) -> None:
    for selector in PLAY_SELECTORS:
        try:
            locator = page.locator(selector)
            if await locator.count():
                await locator.first.click(timeout=700, force=True)
        except Exception:
            pass

    for frame in page.frames:
        try:
            await frame.evaluate(
                """() => {
                    document.querySelectorAll("video").forEach((video) => {
                        try {
                            video.muted = true;
                            video.volume = 0;
                            const result = video.play();
                            if (result && typeof result.catch === "function") {
                                result.catch(() => {});
                            }
                        } catch (_) {}
                    });
                }"""
            )
        except Exception:
            pass


async def read_match_metadata(page: Page, match_url: str) -> dict[str, Any]:
    try:
        data = await page.evaluate(
            r"""() => {
                const clean = (v) => String(v || "").replace(/\s+/g, " ").trim();
                const urls = [];
                const seen = new Set();

                function addUrl(v) {
                    if (!v) return;
                    let value = String(v).trim();
                    if (!value || value.startsWith("data:") || value.startsWith("blob:")) return;
                    try { value = new URL(value, location.href).href; } catch (_) {}
                    if (!seen.has(value)) { seen.add(value); urls.push(value); }
                }

                function inspectImage(img) {
                    [
                        img.currentSrc, img.src,
                        img.getAttribute("src"), img.getAttribute("data-src"),
                        img.getAttribute("data-original"), img.getAttribute("data-lazy-src")
                    ].forEach(addUrl);
                    const sets = [img.getAttribute("srcset"), img.getAttribute("data-srcset")];
                    sets.forEach((set) => {
                        if (!set) return;
                        set.split(",").forEach((part) => addUrl(part.trim().split(/\s+/)[0]));
                    });
                }

                const scopes = [
                    document.querySelector("[class*='match-info']"),
                    document.querySelector("[class*='match-detail']"),
                    document.querySelector("[class*='team']")?.closest("section, article, main, div"),
                    document.querySelector("main"),
                    document.body
                ].filter(Boolean);

                for (const scope of scopes) {
                    scope.querySelectorAll("img").forEach(inspectImage);
                    if (urls.length >= 8) break;
                }

                [
                    document.querySelector("meta[property='og:image']")?.content,
                    document.querySelector("meta[name='twitter:image']")?.content,
                    document.querySelector("link[rel='image_src']")?.href
                ].forEach(addUrl);

                const titleSelectors = [
                    "h1", "[class*='match-title']", "[class*='match-name']",
                    "[class*='event-title']", "h2", "title"
                ];
                let title = "";
                for (const selector of titleSelectors) {
                    const nodes = selector === "title"
                        ? [document.querySelector("title")]
                        : Array.from(document.querySelectorAll(selector));
                    const found = nodes.find((el) => el && /\bvs\b/i.test(clean(el.innerText || el.textContent)));
                    if (found) { title = clean(found.innerText || found.textContent); break; }
                }

                const timeParts = [];
                document.querySelectorAll(
                    "time, [datetime], [data-time], [data-start], [data-date], " +
                    "[class*='time'], [class*='kickoff'], [class*='date']"
                ).forEach((el) => {
                    [
                        el.getAttribute("datetime"), el.getAttribute("data-time"),
                        el.getAttribute("data-start"), el.getAttribute("data-date"),
                        el.innerText, el.textContent
                    ].forEach((v) => { if (v) timeParts.push(clean(v)); });
                });

                document.querySelectorAll("script[type='application/ld+json']").forEach((script) => {
                    try {
                        const raw = JSON.parse(script.textContent || "null");
                        const items = Array.isArray(raw) ? raw : [raw];
                        items.forEach((item) => {
                            if (item && item.startDate) timeParts.push(String(item.startDate));
                            if (!title && item && item.name) title = clean(item.name);
                            if (item && item.image) {
                                (Array.isArray(item.image) ? item.image : [item.image]).forEach(addUrl);
                            }
                        });
                    } catch (_) {}
                });

                const iframeUrls = Array.from(document.querySelectorAll("iframe[src]"))
                    .map((el) => el.src || el.getAttribute("src") || "")
                    .filter(Boolean);

                const sportParts = [
                    document.body?.getAttribute("data-sport"),
                    document.body?.getAttribute("data-category"),
                    document.querySelector("meta[name='description']")?.content,
                    document.querySelector("[data-sport]")?.getAttribute("data-sport"),
                    document.querySelector("[data-category]")?.getAttribute("data-category"),
                    document.querySelector("[class*='breadcrumb']")?.innerText,
                    document.querySelector("[class*='sport-name']")?.innerText,
                    document.querySelector("[class*='category-name']")?.innerText,
                    document.querySelector("[class*='league-name']")?.innerText,
                    title
                ].filter(Boolean).map(clean);

                return {
                    title,
                    time_text: timeParts.join(" | "),
                    logos: urls,
                    iframe_urls: iframeUrls,
                    sport_text: sportParts.join(" | ")
                };
            }"""
        )
        data["logos"] = [absolute_url(str(v), match_url) for v in data.get("logos", []) if v]
        return data
    except Exception:
        return {"title": "", "time_text": "", "logos": [], "iframe_urls": [], "sport_text": ""}


async def fetch_stream(
    context: BrowserContext,
    match: dict[str, Any],
    sem: asyncio.Semaphore,
) -> dict[str, Any]:
    async with sem:
        match_name, time_str, blv_from_link = derive_match_info(
            match["url"], match.get("raw_title", ""), match.get("raw_time", "")
        )
        match["match_name"] = match_name
        match["time"] = time_str
        match["blv"] = blv_from_link
        match["streams"] = []
        match["stream_urls"] = []
        match["errors"] = []
        match["sport_group"] = classify_sport(
            match.get("sport_hint", ""),
            match.get("card_text", ""),
            match.get("raw_title", ""),
            match.get("url", ""),
            default=match.get("sport_group", "Bóng đá"),
        )

        scan_index = int(match.get("_scan_index", 0))
        scan_total = int(match.get("_scan_total", 0))
        prefix = f"[{scan_index}/{scan_total}] " if scan_index and scan_total else ""
        print(
            f"-> {prefix}Đang quét [{match['sport_group']}]: {match_name[:90]}",
            flush=True,
        )
        page = await context.new_page()
        await install_route_filter(page, homepage=False)

        stream_map: dict[str, dict[str, Any]] = {}
        first_stream_at: float | None = None
        rate_limit_urls: set[str] = set()

        def capture_url(
            raw_url: str,
            source: str,
            headers: dict[str, str] | None = None,
            frame_url: str = "",
            status: int | None = None,
            content_type: str = "",
        ) -> None:
            nonlocal first_stream_at
            normalized_headers = {
                str(k).lower(): str(v) for k, v in (headers or {}).items()
            }
            hint = stream_referer_hint(raw_url, frame_url)

            for stream_url in extract_stream_urls(raw_url, content_type):
                normalized = decode_url_repeatedly(stream_url)
                entry = stream_map.setdefault(
                    normalized,
                    {
                        "url": normalized,
                        "referer": "",
                        "origin": "",
                        "user_agent": "",
                        "status": None,
                        "statuses": [],
                        "content_type": "",
                        "sources": [],
                    },
                )

                referer = normalize_playback_referer(
                    normalized_headers.get("referer", "") or hint
                )
                # Không tự tạo Origin. VLC thử nghiệm chạy với Referer + User-Agent;
                # Origin dư thừa có thể làm CDN từ chối. Chỉ lưu nếu request thật có gửi.
                origin = normalized_headers.get("origin", "")
                user_agent = normalized_headers.get("user-agent", "") or UA

                if referer:
                    entry["referer"] = referer
                if origin:
                    entry["origin"] = origin
                if user_agent:
                    entry["user_agent"] = user_agent
                if status is not None:
                    entry["status"] = status
                    if status not in entry["statuses"]:
                        entry["statuses"].append(status)
                if content_type:
                    entry["content_type"] = content_type
                if source not in entry["sources"]:
                    entry["sources"].append(source)

                if first_stream_at is None:
                    first_stream_at = time.monotonic()
                if len(entry["sources"]) == 1:
                    print(f"   🎯 [{source}] {normalized}")

        def handle_request(request: Any) -> None:
            try:
                frame_url = request.frame.url if request.frame else ""
            except Exception:
                frame_url = ""
            capture_url(
                request.url,
                f"request/{request.resource_type}",
                headers=request.headers,
                frame_url=frame_url,
            )

        def handle_response(response: Any) -> None:
            try:
                if response.status == 429 and response.url not in rate_limit_urls:
                    rate_limit_urls.add(response.url)
                    match["errors"].append(
                        f"HTTP 429 (tiếp tục quét, không restart): {response.url}"
                    )
                    print(f"   ⚠️ HTTP 429 nhưng vẫn tiếp tục quét full: {response.url}")

                req = response.request
                frame_url = req.frame.url if req.frame else ""
                content_type = response.headers.get("content-type", "")
                capture_url(
                    response.url,
                    "response",
                    headers=req.headers,
                    frame_url=frame_url,
                    status=response.status,
                    content_type=content_type,
                )
            except Exception:
                capture_url(response.url, "response", status=response.status)

        def handle_page_error(error: Any) -> None:
            match["errors"].append(f"JS: {error}")

        def handle_console(message: Any) -> None:
            if message.type in {"error", "warning"}:
                text = str(message.text)
                if len(text) <= 500:
                    match["errors"].append(f"console/{message.type}: {text}")

        page.on("request", handle_request)
        page.on("response", handle_response)
        page.on("pageerror", handle_page_error)
        page.on("console", handle_console)

        try:
            await page.goto(match["url"], wait_until="domcontentloaded", timeout=30000)
            await page.wait_for_timeout(1200)

            metadata = await read_match_metadata(page, match["url"])
            if metadata.get("title"):
                better_name = clean_match_name(metadata["title"], match["url"])
                if re.search(r"\bvs\b", better_name, re.I):
                    match["match_name"] = better_name
            if not match.get("time"):
                match["time"] = extract_time(metadata.get("time_text", ""))

            match["sport_group"] = classify_sport(
                match.get("sport_hint", ""),
                metadata.get("sport_text", ""),
                match.get("card_text", ""),
                match.get("match_name", ""),
                match.get("url", ""),
                default=match.get("sport_group", "Bóng đá"),
            )

            logo_candidates = list(match.get("team_logos") or [])
            if match.get("logo"):
                logo_candidates.insert(0, match["logo"])
            logo_candidates.extend(metadata.get("logos") or [])
            match["team_logos"] = [
                absolute_url(v, match["url"]) for v in logo_candidates if v
            ]
            match["logo"] = choose_logo(match["team_logos"], match["url"])

            for iframe_url in metadata.get("iframe_urls") or []:
                capture_url(iframe_url, "iframe/src", frame_url=iframe_url)

            deadline = time.monotonic() + STREAM_WAIT_SECONDS
            while time.monotonic() < deadline:
                await stimulate_player(page)
                for candidate in await collect_dom_stream_candidates(page):
                    capture_url(
                        candidate["url"],
                        "dom/performance",
                        frame_url=candidate.get("frame_url", ""),
                    )

                if (
                    not FULL_SCAN
                    and first_stream_at is not None
                    and time.monotonic() - first_stream_at >= EXTRA_WAIT_AFTER_FIRST_STREAM
                ):
                    break
                await page.wait_for_timeout(1000)

        except Exception as exc:
            error_text = f"{type(exc).__name__}: {exc}"
            match["errors"].append(error_text)
            print(f"   ❌ {match_name[:70]} | {error_text}")
        finally:
            try:
                for candidate in await collect_dom_stream_candidates(page):
                    capture_url(
                        candidate["url"],
                        "final-scan",
                        frame_url=candidate.get("frame_url", ""),
                    )
            except Exception:
                pass
            await page.close()

        streams = []
        for entry in stream_map.values():
            # Header fallback đúng player embed, không dùng nhầm origin live03.
            entry["referer"] = normalize_playback_referer(
                entry.get("referer") or PLAYER_ORIGIN_FALLBACK + "/"
            )
            if not entry.get("user_agent"):
                entry["user_agent"] = UA

            status = entry.get("status")
            statuses = [int(value) for value in (entry.get("statuses") or [])]

            # 404/410 là link đã mất rõ ràng nên mới loại. Các mã 401/403/429/5xx
            # vẫn được giữ vì request trong Chromium có thể bị chặn, trong khi player
            # phát được khi gửi đúng Referer + User-Agent. Đây chính là trường hợp
            # URL FLV thử thủ công bằng VLC của người dùng.
            terminal_statuses = {404, 410}
            if statuses and all(value in terminal_statuses for value in statuses):
                match["errors"].append(
                    f"Stream chỉ trả {statuses}, loại link đã mất: {entry['url']}"
                )
                print(f"   ⚠️ Loại stream HTTP {statuses}: {entry['url']}")
                continue

            if status is not None and int(status) >= 400:
                match["errors"].append(
                    f"Stream HTTP {status} nhưng vẫn giữ để phát kèm header: {entry['url']}"
                )
                print(
                    f"   🛡️ Giữ stream HTTP {status}; Android/VLC sẽ gửi "
                    f"Referer + User-Agent: {entry['url']}"
                )
            streams.append(entry)

        match["streams"] = sorted(streams, key=lambda item: item["url"])
        match["stream_urls"] = [item["url"] for item in match["streams"]]

        if match["streams"]:
            for entry in match["streams"]:
                state = entry.get("status") or "chưa có status"
                print(
                    f"   ✅ Stream {state} | referer={entry.get('referer', '')} | "
                    f"logo={'có' if match.get('logo') else 'không'} | "
                    f"giờ={match.get('time') or 'không rõ'}"
                )
        else:
            print(f"   ⚠️ Không thấy m3u8/flv: {match_name[:85]}")

        return match


async def collect_home_links(context: BrowserContext) -> list[dict[str, Any]]:
    page = await context.new_page()
    await install_route_filter(page, homepage=True)
    print(f"👉 Đang mở trang chủ: {TARGET_URL}")

    try:
        await page.goto(TARGET_URL, wait_until="domcontentloaded", timeout=30000)
        await page.wait_for_timeout(HOME_WAIT_MS)

        for _ in range(5):
            await page.evaluate("window.scrollBy(0, Math.max(700, window.innerHeight));")
            await page.wait_for_timeout(700)

        result = await page.evaluate(
            r"""() => {
                const items = [];
                const seen = new Set();
                const clean = (v) => String(v || "").replace(/\s+/g, " ").trim();

                function normalizeHref(value) {
                    try { return new URL(value, location.href).href; }
                    catch (_) { return ""; }
                }

                function isMatchHref(value) {
                    const href = normalizeHref(value);
                    if (!href) return false;
                    try {
                        const path = new URL(href).pathname;
                        return /^\/live\/\d+(?:\/|$)/i.test(path) ||
                            path.includes("/truc-tiep/") || path.includes("/room/");
                    } catch (_) { return false; }
                }

                function imageCandidates(scope) {
                    const scored = [];
                    if (!scope) return [];
                    scope.querySelectorAll("img").forEach((img, index) => {
                        const context = clean([
                            img.alt, img.title, img.className,
                            img.parentElement?.className, img.parentElement?.parentElement?.className
                        ].join(" ")).toLowerCase();
                        let score = 0;
                        if (/team|club|home|away|doi|đội/.test(context)) score += 12;
                        if (/logo/.test(context)) score += 4;
                        if (/avatar|blv|comment|banner|advert|ads|flag/.test(context)) score -= 20;
                        if ((img.naturalWidth || img.width || 0) <= 256) score += 2;
                        score -= index * 0.01;

                        const values = [
                            img.currentSrc, img.src,
                            img.getAttribute("src"), img.getAttribute("data-src"),
                            img.getAttribute("data-original"), img.getAttribute("data-lazy-src")
                        ];
                        [img.getAttribute("srcset"), img.getAttribute("data-srcset")]
                            .filter(Boolean)
                            .forEach((set) => set.split(",").forEach((part) =>
                                values.push(part.trim().split(/\s+/)[0])
                            ));

                        values.filter(Boolean).forEach((value) => {
                            try { value = new URL(value, location.href).href; } catch (_) {}
                            scored.push({ value, score });
                        });
                    });

                    scope.querySelectorAll("[style*='background-image']").forEach((el) => {
                        const match = (el.style.backgroundImage || "").match(/url\(["']?([^"')]+)["']?\)/i);
                        if (match) {
                            let value = match[1];
                            try { value = new URL(value, location.href).href; } catch (_) {}
                            scored.push({ value, score: 3 });
                        }
                    });

                    const out = [];
                    const unique = new Set();
                    scored.sort((a, b) => b.score - a.score).forEach((item) => {
                        if (!unique.has(item.value)) { unique.add(item.value); out.push(item.value); }
                    });
                    return out;
                }

                function findContainer(a) {
                    return a.closest(
                        "[data-match-id], [data-event-id], [class*='match-card'], " +
                        "[class*='match-item'], [class*='game-card'], [class*='fixture'], article, li"
                    ) || a.parentElement?.parentElement || a.parentElement || a;
                }

                function sportContext(a, container) {
                    const parts = [];
                    const add = (value) => {
                        const fixed = clean(value);
                        if (fixed && fixed.length <= 300 && !parts.includes(fixed)) parts.push(fixed);
                    };
                    const inspect = (node) => {
                        if (!node) return;
                        [
                            node.getAttribute?.("data-sport"),
                            node.getAttribute?.("data-category"),
                            node.getAttribute?.("data-type"),
                            node.getAttribute?.("aria-label"),
                            node.id,
                            node.className
                        ].forEach(add);
                        const heading = node.querySelector?.(
                            ":scope > h1, :scope > h2, :scope > h3, :scope > h4, " +
                            ":scope > [class*='sport-title'], :scope > [class*='category-title']"
                        );
                        add(heading?.innerText || heading?.textContent);
                    };

                    inspect(a);
                    inspect(container);
                    let node = container;
                    for (let depth = 0; node && depth < 6; depth += 1, node = node.parentElement) {
                        inspect(node);
                        let previous = node.previousElementSibling;
                        for (let step = 0; previous && step < 3; step += 1, previous = previous.previousElementSibling) {
                            if (/^H[1-6]$/.test(previous.tagName || "") ||
                                /sport|category|tab|section/i.test(String(previous.className || ""))) {
                                add(previous.innerText || previous.textContent);
                            }
                        }
                    }
                    return parts.join(" | ");
                }

                function addItem(
                    hrefValue,
                    titleValue = "",
                    cardText = "",
                    timeValue = "",
                    logos = [],
                    sportHint = ""
                ) {
                    const href = normalizeHref(hrefValue);
                    if (!isMatchHref(href) || seen.has(href)) return;
                    seen.add(href);
                    const parts = new URL(href).pathname.split("/").filter(Boolean);
                    const fallback = decodeURIComponent(parts[parts.length - 1] || href)
                        .replace(/-vs-/gi, " vs ").replace(/-/g, " ");
                    items.push({
                        url: href,
                        raw_title: clean(titleValue || cardText || fallback),
                        card_text: clean(cardText),
                        raw_time: clean(timeValue || cardText),
                        logo: logos[0] || "",
                        team_logos: logos.slice(0, 8),
                        sport_hint: clean(sportHint),
                    });
                }

                document.querySelectorAll("a[href]").forEach((a) => {
                    const href = a.href || a.getAttribute("href") || "";
                    if (!isMatchHref(href)) return;
                    const container = findContainer(a);
                    const cardText = clean(container?.innerText || a.innerText || "");
                    const sportHint = sportContext(a, container);

                    const timeEl = container?.querySelector(
                        "time, [datetime], [data-time], [data-start], [class*='time'], [class*='kickoff']"
                    );
                    const timeValue = clean([
                        timeEl?.getAttribute("datetime"), timeEl?.getAttribute("data-time"),
                        timeEl?.getAttribute("data-start"), timeEl?.innerText
                    ].filter(Boolean).join(" "));

                    const titleNode = Array.from(container?.querySelectorAll(
                        "h1, h2, h3, [class*='match-title'], [class*='match-name'], [class*='team-name']"
                    ) || []).find((el) => /\bvs\b/i.test(clean(el.innerText || el.textContent)));

                    addItem(
                        href,
                        clean(titleNode?.innerText || titleNode?.textContent || a.innerText || a.title || a.getAttribute("aria-label")),
                        cardText,
                        timeValue,
                        imageCandidates(container),
                        sportHint
                    );
                });

                const htmlText = document.documentElement?.innerHTML || "";
                const normalizedHtml = htmlText.replace(/\\\//g, "/")
                    .replace(/&amp;/g, "&").replace(/\\u002F/gi, "/");
                const patterns = [
                    /https?:\/\/[^"' <>\n\r]+\/live\/\d+\/[^"' <>\n\r]+/gi,
                    /\/live\/\d+\/[a-z0-9][a-z0-9._~!$&'()*+,;=:@%\/-]*/gi,
                    /https?:\/\/[^"' <>\n\r]+\/(?:truc-tiep|room)\/[^"' <>\n\r]+/gi,
                    /\/(?:truc-tiep|room)\/[^"' <>\n\r]+/gi,
                ];
                for (const pattern of patterns) {
                    (normalizedHtml.match(pattern) || []).forEach((href) => addItem(href));
                }

                const anchors = Array.from(document.querySelectorAll("a[href]"));
                return {
                    items,
                    diagnostics: {
                        final_url: location.href,
                        title: document.title || "",
                        anchor_count: anchors.length,
                        html_length: normalizedHtml.length,
                        sample_hrefs: anchors.slice(0, 20).map((a) => a.href || "")
                    }
                };
            }"""
        )

        links = list(result.get("items") or [])
        for item in links:
            item["sport_group"] = classify_sport(
                item.get("sport_hint", ""),
                item.get("card_text", ""),
                item.get("raw_title", ""),
                item.get("url", ""),
            )
        diagnostics = result.get("diagnostics") or {}
        print(
            "ℹ️ Trang chủ: "
            f"title={diagnostics.get('title', '')!r} | "
            f"anchors={diagnostics.get('anchor_count', 0)} | "
            f"html={diagnostics.get('html_length', 0)} ký tự | "
            f"match_links={len(links)}"
        )

        if links:
            counts = Counter(item.get("sport_group", "Khác") for item in links)
            summary = " | ".join(
                f"{group}={counts[group]}" for group in SPORT_GROUP_ORDER if counts[group]
            )
            print(f"📂 Phân loại link trang chủ: {summary}", flush=True)

        if not links:
            try:
                Path(OUTPUT_HOME_DEBUG_HTML).write_text(await page.content(), encoding="utf-8")
                await page.screenshot(path=OUTPUT_HOME_DEBUG_PNG, full_page=True)
                print(f"⚠️ Đã lưu trang debug: {OUTPUT_HOME_DEBUG_HTML}, {OUTPUT_HOME_DEBUG_PNG}")
            except Exception as debug_exc:
                print(f"⚠️ Không lưu được trang debug: {debug_exc}")
        return links

    except Exception as exc:
        print(f"❌ Không lấy được danh sách trang chủ: {type(exc).__name__}: {exc}")
        return []
    finally:
        await page.close()


def escape_m3u_text(value: str) -> str:
    return re.sub(r"[\r\n]+", " ", value or "").replace('"', "'").strip()


def header_json(user_agent: str, referer: str) -> str:
    values = {"User-Agent": user_agent}
    if referer:
        values["Referer"] = referer
    return json.dumps(values, ensure_ascii=False, separators=(",", ":"))


def escape_pipe_header(value: str) -> str:
    """Mã hóa giá trị protocol-option để URL không vỡ bởi khoảng trắng, &, | hoặc %."""
    return quote(clean_text(value), safe=":/().,;=-_")


def android_stream_url(stream_url: str, user_agent: str, referer: str) -> str:
    """
    Header syntax understood by many Android IPTV players:
      URL|User-Agent=...&Referer=...

    Keep EXTVLCOPT too because TiviMate versions differ in which syntax they honor.
    """
    headers = [f"User-Agent={escape_pipe_header(user_agent)}"]
    if referer:
        headers.append(f"Referer={escape_pipe_header(referer)}")
    return stream_url + "|" + "&".join(headers)


def write_outputs(results: list[dict[str, Any]]) -> tuple[int, int]:
    """
    Tạo 3 playlist:
      - chuoichien_live.m3u: playlist phổ thông, URL nguyên bản + EXTHTTP/EXTVLCOPT.
      - chuoichien_live_pipe.m3u: biến thể Kodi-style URL|Header=Value.
      - chuoichien_live_vlc.m3u: URL nguyên bản + EXTVLCOPT dành riêng VLC.

    Không gắn pipe headers vào playlist mặc định vì nhiều IPTV player Android
    coi phần sau dấu | là một phần URL và báo lỗi phát kênh.
    """
    universal_lines = ["#EXTM3U"]
    pipe_lines = ["#EXTM3U"]
    vlc_lines = ["#EXTM3U"]

    written_streams: set[str] = set()
    match_keys_with_streams: set[str] = set()
    count_links = 0

    sorted_results = sorted(
        results,
        key=lambda item: (
            SPORT_GROUP_RANK.get(item.get("sport_group", "Khác"), 999),
            item.get("time") or "99:99",
            clean_text(item.get("match_name") or item.get("raw_title") or "").lower(),
        ),
    )

    group_stream_counts: Counter[str] = Counter()

    for result in sorted_results:
        streams = result.get("streams") or [
            {"url": value} for value in (result.get("stream_urls") or [])
        ]
        if not streams:
            continue

        match_name = result.get("match_name") or result.get("raw_title") or "Chuối Chiên TV"
        time_str = result.get("time") or ""
        blv = result.get("blv") or ""
        sport_group = result.get("sport_group") or classify_sport(
            result.get("sport_hint", ""),
            result.get("card_text", ""),
            match_name,
            result.get("url", ""),
        )
        if sport_group not in SPORT_GROUP_RANK:
            sport_group = "Khác"
        logo = choose_logo(
            [result.get("logo", "")] + list(result.get("team_logos") or []),
            result.get("url") or TARGET_URL,
        )

        display_base = f"[{time_str}] {match_name}" if time_str else match_name
        if blv and blv.lower() not in display_base.lower():
            display_base += f" [BLV {blv}]"
        display_base = escape_m3u_text(display_base)
        logo = escape_m3u_text(logo)

        unique_streams = [item for item in streams if item.get("url") not in written_streams]
        if not unique_streams:
            continue

        match_keys_with_streams.add(f"{match_name}|{blv}|{time_str}")
        for index, stream_info in enumerate(unique_streams, start=1):
            stream_url = decode_url_repeatedly(stream_info.get("url", ""))
            if not stream_url:
                continue
            written_streams.add(stream_url)

            display_name = display_base
            if len(unique_streams) > 1:
                display_name += f" (Luồng {index})"

            referer = normalize_playback_referer(
                stream_info.get("referer") or PLAYER_ORIGIN_FALLBACK + "/"
            )
            user_agent = clean_text(stream_info.get("user_agent") or UA)
            kind = stream_kind(stream_url, stream_info.get("content_type", ""))
            if kind:
                display_name += f" [{kind.upper()}]"

            channel_id = channel_id_for(result, stream_url, index)
            attributes = (
                f'tvg-id="{escape_m3u_text(channel_id)}" '
                f'tvg-name="{escape_m3u_text(display_base)}" '
                f'group-title="{escape_m3u_text(sport_group)}"'
            )
            if logo:
                attributes += f' tvg-logo="{logo}"'
            extinf = f"#EXTINF:-1 {attributes},{display_name}"

            universal_lines.extend([
                extinf,
                f"#EXTVLCOPT:http-referrer={referer}",
                f"#EXTVLCOPT:http-user-agent={user_agent}",
                "#EXTVLCOPT:http-reconnect=true",
                f"#EXTHTTP:{header_json(user_agent, referer)}",
                stream_url,
            ])

            pipe_lines.extend([
                extinf,
                f"#EXTVLCOPT:http-referrer={referer}",
                f"#EXTVLCOPT:http-user-agent={user_agent}",
                "#EXTVLCOPT:http-reconnect=true",
                f"#EXTHTTP:{header_json(user_agent, referer)}",
                android_stream_url(stream_url, user_agent, referer),
            ])

            vlc_lines.extend([
                extinf,
                f"#EXTVLCOPT:http-referrer={referer}",
                f"#EXTVLCOPT:http-user-agent={user_agent}",
                "#EXTVLCOPT:http-reconnect=true",
                stream_url,
            ])

            group_stream_counts[sport_group] += 1
            count_links += 1

    Path(OUTPUT_DEBUG).write_text(
        json.dumps(results, ensure_ascii=False, indent=2), encoding="utf-8"
    )

    output_sets = (
        (Path(OUTPUT_M3U), universal_lines, "phổ thông"),
        (Path(OUTPUT_PIPE_M3U), pipe_lines, "pipe/Kodi"),
        (Path(OUTPUT_VLC_M3U), vlc_lines, "VLC"),
    )

    if count_links:
        for path, lines, _label in output_sets:
            path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    else:
        for path, _lines, label in output_sets:
            if path.exists():
                print(f"⚠️ Không có link mới; giữ nguyên playlist {label}: {path.resolve()}")
            else:
                path.write_text("#EXTM3U\n", encoding="utf-8")
                print(f"⚠️ Đã tạo playlist {label} rỗng: {path.resolve()}")

    if count_links:
        m3u8_count = sum(
            1 for line in vlc_lines if line.startswith("http") and stream_kind(line) == "m3u8"
        )
        flv_count = sum(
            1 for line in vlc_lines if line.startswith("http") and stream_kind(line) == "flv"
        )
        print(f"📊 Playlist: M3U8={m3u8_count} | FLV={flv_count}")
        group_summary = " | ".join(
            f"{group}={group_stream_counts[group]}"
            for group in SPORT_GROUP_ORDER if group_stream_counts[group]
        )
        if group_summary:
            print(f"📂 Thư mục playlist: {group_summary}")
        print(f"📺 Mặc định Android/IPTV: {Path(OUTPUT_M3U).resolve()}")
        print(f"📺 Pipe/Kodi tùy chọn: {Path(OUTPUT_PIPE_M3U).resolve()}")
        print(f"📺 VLC: {Path(OUTPUT_VLC_M3U).resolve()}")

    return len(match_keys_with_streams), count_links


async def progress_heartbeat(tasks: list[asyncio.Task[Any]], total: int) -> None:
    """In tiến trình đều đặn để GitHub Actions không đứng im trong lúc các tab đang chờ."""
    started = time.monotonic()
    try:
        while True:
            await asyncio.sleep(5)
            completed = sum(task.done() for task in tasks)
            if completed >= total:
                return
            active = min(CONCURRENCY_LIMIT, total - completed)
            waiting = max(0, total - completed - active)
            elapsed = int(time.monotonic() - started)
            print(
                f"⏳ Tiến trình realtime: xong {completed}/{total} | "
                f"đang/chờ tối đa {active}/{waiting} | đã chạy {elapsed}s",
                flush=True,
            )
    except asyncio.CancelledError:
        return


async def main() -> None:
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(line_buffering=True, write_through=True)
        except Exception:
            pass

    print(f"🥷 KHỞI ĐỘNG CHUỐI CHIÊN STREAM SCANNER - {SCANNER_VERSION}", flush=True)
    print(
        "ℹ️ Test riêng một trận:\n"
        '   python main.py "https://live03.chuoichientv.me/live/1524177/capalaba-vs-holland-park-hawks"'
    )
    print(
        f"ℹ️ Chế độ quét: {'FULL toàn bộ thời gian' if FULL_SCAN else 'dừng sớm'} | "
        f"định dạng={','.join(STREAM_EXTENSIONS)} | chờ mỗi trận={STREAM_WAIT_SECONDS}s"
    )

    direct_urls = [
        arg.strip() for arg in sys.argv[1:]
        if arg.strip().startswith(("http://", "https://"))
    ]

    async with async_playwright() as playwright:
        browser = await playwright.chromium.launch(
            headless=HEADLESS,
            args=[
                "--disable-blink-features=AutomationControlled",
                "--no-sandbox",
                "--mute-audio",
                "--autoplay-policy=no-user-gesture-required",
                "--disable-dev-shm-usage",
            ],
        )
        context = await browser.new_context(
            viewport={"width": 1366, "height": 768},
            user_agent=UA,
            locale="vi-VN",
            timezone_id="Asia/Ho_Chi_Minh",
            ignore_https_errors=True,
            service_workers="block",
            extra_http_headers={
                "Accept-Language": "vi-VN,vi;q=0.9,en-US;q=0.8,en;q=0.7"
            },
        )

        if direct_urls:
            links = []
            for url in direct_urls:
                match_name, _, _ = derive_match_info(url)
                links.append({
                    "url": url,
                    "raw_title": match_name,
                    "raw_time": "",
                    "logo": "",
                    "team_logos": [],
                    "sport_hint": "",
                    "sport_group": classify_sport(match_name, url),
                })
            print(f"✅ Chế độ test trực tiếp: {len(links)} URL.")
        else:
            links = await collect_home_links(context)

        if not links:
            print("❌ Không tìm thấy link trận/phòng nào.")
            write_outputs([])
            await context.close()
            await browser.close()
            return

        print(
            f"✅ Tìm thấy {len(links)} link trận/phòng. "
            f"Bắt đầu quét tối đa {CONCURRENCY_LIMIT} trang cùng lúc..."
        )
        semaphore = asyncio.Semaphore(CONCURRENCY_LIMIT)
        total_links = len(links)
        tasks: list[asyncio.Task[dict[str, Any]]] = []
        for index, match in enumerate(links, start=1):
            match["_scan_index"] = index
            match["_scan_total"] = total_links
            tasks.append(asyncio.create_task(fetch_stream(context, match, semaphore)))

        heartbeat = asyncio.create_task(progress_heartbeat(tasks, total_links))
        results: list[dict[str, Any]] = []
        completed = 0
        try:
            for future in asyncio.as_completed(tasks):
                result = await future
                results.append(result)
                completed += 1
                found = len(result.get("streams") or [])
                print(
                    f"📈 Hoàn thành {completed}/{total_links}: "
                    f"[{result.get('sport_group', 'Khác')}] "
                    f"{result.get('match_name', '')[:70]} | stream={found}",
                    flush=True,
                )
        finally:
            heartbeat.cancel()
            await asyncio.gather(heartbeat, return_exceptions=True)

        count_matches, count_links = write_outputs(results)

        if count_links:
            print(f"\n🎉 HOÀN TẤT: lấy được {count_links} link từ {count_matches} trận/phòng.")
            print(f"📺 Playlist mặc định: {Path(OUTPUT_M3U).resolve()}")
            print(f"📺 Playlist pipe/Kodi: {Path(OUTPUT_PIPE_M3U).resolve()}")
            print(f"📺 Playlist VLC: {Path(OUTPUT_VLC_M3U).resolve()}")
        else:
            print("\n❌ Không bắt được m3u8/flv nào.")
        print(f"🧾 Nhật ký chi tiết: {Path(OUTPUT_DEBUG).resolve()}")

        await context.close()
        await browser.close()


if __name__ == "__main__":
    asyncio.run(main())
