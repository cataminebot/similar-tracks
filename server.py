#!/usr/bin/env python3
"""
Similar Track Finder — Beatport + SoundCloud + Bandcamp
Searches three platforms simultaneously for tracks similar to a given input.
"""

import http.server
import json
import math
import os
import re
import time
import urllib.parse
import urllib.request
import ssl
import hashlib
import html as html_module
from concurrent.futures import ThreadPoolExecutor, as_completed

PORT = int(os.environ.get("PORT", 8899))
UA = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"

_ssl = ssl.create_default_context()
_ssl.check_hostname = False
_ssl.verify_mode = ssl.CERT_NONE

_cache = {}
CACHE_TTL = 3600

# ═══════════════════════════════════════
#  Camelot Wheel
# ═══════════════════════════════════════

KEY_TO_CAMELOT = {}
for _keys, _cam in [
    (["G# minor", "Ab minor", "G# Minor", "Ab Minor"], "1A"),
    (["B major", "B Major"], "1B"),
    (["Eb minor", "D# minor", "Eb Minor", "D# Minor"], "2A"),
    (["F# major", "Gb major", "F# Major", "Gb Major"], "2B"),
    (["Bb minor", "A# minor", "Bb Minor", "A# Minor"], "3A"),
    (["Db major", "C# major", "Db Major", "C# Major"], "3B"),
    (["F minor", "F Minor"], "4A"),
    (["Ab major", "G# major", "Ab Major", "G# Major"], "4B"),
    (["C minor", "C Minor"], "5A"),
    (["Eb major", "D# major", "Eb Major", "D# Major"], "5B"),
    (["G minor", "G Minor"], "6A"),
    (["Bb major", "A# major", "Bb Major", "A# Major"], "6B"),
    (["D minor", "D Minor"], "7A"),
    (["F major", "F Major"], "7B"),
    (["A minor", "A Minor"], "8A"),
    (["C major", "C Major"], "8B"),
    (["E minor", "E Minor"], "9A"),
    (["G major", "G Major"], "9B"),
    (["B minor", "B Minor"], "10A"),
    (["D major", "D Major"], "10B"),
    (["F# minor", "Gb minor", "F# Minor", "Gb Minor"], "11A"),
    (["A major", "A Major"], "11B"),
    (["C# minor", "Db minor", "C# Minor", "Db Minor"], "12A"),
    (["E major", "E Major"], "12B"),
]:
    for k in _keys:
        KEY_TO_CAMELOT[k] = _cam


def normalize_key(key_str):
    if not key_str:
        return None
    key_str = key_str.strip()
    if re.match(r'^\d{1,2}[AB]$', key_str):
        return key_str
    return KEY_TO_CAMELOT.get(key_str)


def camelot_distance(k1, k2):
    if not k1 or not k2:
        return None
    m1 = re.match(r'^(\d{1,2})([AB])$', k1)
    m2 = re.match(r'^(\d{1,2})([AB])$', k2)
    if not m1 or not m2:
        return None
    n1, l1 = int(m1.group(1)), m1.group(2)
    n2, l2 = int(m2.group(1)), m2.group(2)
    return min(abs(n1 - n2), 12 - abs(n1 - n2)) + (0 if l1 == l2 else 1)


def key_score(k1, k2):
    d = camelot_distance(k1, k2)
    if d is None:
        return 0.5
    return {0: 1.0, 1: 0.85, 2: 0.5}.get(d, 0.1)


def bpm_score(bpm1, bpm2):
    if not bpm1 or not bpm2:
        return 0.5
    diff = min(abs(bpm1 - bpm2), abs(bpm1 - bpm2 * 2), abs(bpm1 * 2 - bpm2))
    return math.exp(-(diff ** 2) / 32)


# ── Genre affinity for Beatport ──
GENRE_AFFINITY = {
    (12, 93): 0.8, (12, 15): 0.6, (12, 90): 0.5, (12, 5): 0.7, (12, 37): 0.5, (12, 89): 0.4,
    (93, 37): 0.6, (93, 3): 0.6, (93, 15): 0.5, (93, 5): 0.5,
    (11, 5): 0.7, (11, 14): 0.7, (11, 97): 0.6, (11, 89): 0.4, (11, 12): 0.3,
    (90, 15): 0.8, (90, 12): 0.5, (90, 92): 0.5, (90, 6): 0.4, (90, 3): 0.5,
    (15, 90): 0.8, (15, 12): 0.6, (15, 5): 0.6,
    (89, 12): 0.5, (89, 5): 0.6, (89, 11): 0.4,
    (5, 12): 0.7, (5, 11): 0.7, (5, 15): 0.6, (5, 89): 0.6,
    (14, 11): 0.7, (14, 92): 0.6, (14, 6): 0.4,
}


def genre_score(g1, g2):
    if not g1 or not g2:
        return 0.5
    if g1 == g2:
        return 1.0
    return GENRE_AFFINITY.get((g1, g2), GENRE_AFFINITY.get((g2, g1), 0.15))


# ── Similarity scoring ──

def compute_similarity_beatport(source, track):
    gs = genre_score(source.get("genre_id"), track.get("genre_id"))
    bs = bpm_score(source.get("bpm"), track.get("bpm"))
    ks = key_score(normalize_key(source.get("key", "")), normalize_key(track.get("key", "")))
    lb = 1.0 if source.get("label") and track.get("label") and source["label"].lower() == track["label"].lower() else 0
    ab = 0.5 if _artist_overlap(source, track) else 0
    return round((gs * 0.28 + bs * 0.28 + ks * 0.24 + lb * 0.12 + ab * 0.08) * 100, 1)


def compute_similarity_text(source, track):
    """Similarity for platforms without BPM/key."""
    src_tags = _extract_tags(source)
    trk_tags = _extract_tags(track)
    tag_sim = len(src_tags & trk_tags) / max(len(src_tags | trk_tags), 1) if (src_tags or trk_tags) else 0.3
    artist_sim = 1.0 if _artist_overlap(source, track) else 0
    src_tokens = _title_tokens(source.get("title", ""))
    trk_tokens = _title_tokens(track.get("title", ""))
    title_sim = len(src_tokens & trk_tokens) / max(len(src_tokens | trk_tokens), 1) if src_tokens else 0
    lb = 1.0 if source.get("label") and track.get("label") and source["label"].lower() == track["label"].lower() else 0
    return round((tag_sim * 0.40 + artist_sim * 0.25 + title_sim * 0.20 + lb * 0.15) * 100, 1)


def _artist_overlap(source, track):
    src = set(a.lower().strip() for a in (source.get("artist_list") or [source.get("artists", "")]) if a)
    trk = set(a.lower().strip() for a in (track.get("artist_list") or [track.get("artists", "")]) if a)
    return bool(src and trk and src & trk)


STOP_WORDS = {'the', 'and', 'of', 'a', 'in', 'to', 'for', 'is', 'on', 'at', 'by', 'with'}


def _extract_tags(track):
    raw = f"{track.get('genre', '')} {track.get('tags', '')}".lower()
    return set(re.findall(r'[a-z]+', raw)) - STOP_WORDS


def _title_tokens(title):
    clean = re.sub(r'\b(original|mix|remix|extended|radio|edit|feat|ft|official|version)\b', '', title.lower())
    return set(re.findall(r'[a-z]{3,}', clean))


# ═══════════════════════════════════════
#  HTTP helpers
# ═══════════════════════════════════════

def fetch_url(url, accept="text/html"):
    ck = hashlib.md5(url.encode()).hexdigest()
    if ck in _cache and time.time() < _cache[ck]["exp"]:
        return _cache[ck]["data"]
    req = urllib.request.Request(url)
    req.add_header("User-Agent", UA)
    req.add_header("Accept", accept)
    try:
        resp = urllib.request.urlopen(req, timeout=15, context=_ssl)
        data = resp.read().decode("utf-8", errors="replace")
        _cache[ck] = {"data": data, "exp": time.time() + CACHE_TTL}
        return data
    except Exception as e:
        print(f"  [FETCH ERR] {url[:80]}: {e}")
        return None


def fetch_json(url):
    text = fetch_url(url, "application/json")
    try:
        return json.loads(text) if text else None
    except:
        return None


def post_json(url, payload):
    ck = hashlib.md5((url + json.dumps(payload)).encode()).hexdigest()
    if ck in _cache and time.time() < _cache[ck]["exp"]:
        return _cache[ck]["data"]
    body = json.dumps(payload).encode()
    req = urllib.request.Request(url, data=body, method="POST")
    req.add_header("User-Agent", UA)
    req.add_header("Content-Type", "application/json")
    try:
        resp = urllib.request.urlopen(req, timeout=15, context=_ssl)
        data = json.loads(resp.read().decode())
        _cache[ck] = {"data": data, "exp": time.time() + CACHE_TTL}
        return data
    except Exception as e:
        print(f"  [POST ERR] {url}: {e}")
        return None


# ═══════════════════════════════════════
#  BEATPORT SCRAPER
# ═══════════════════════════════════════

def scrape_beatport_search(query, per_page=50):
    encoded = urllib.parse.quote(query)
    url = f"https://www.beatport.com/search?q={encoded}&type=tracks"
    html = fetch_url(url)
    if not html:
        return []
    return _parse_bp_next_data(html)


def scrape_beatport_genre(genre_slug, genre_id, bpm_low=None, bpm_high=None):
    params = {}
    if bpm_low:
        params["bpm-low"] = bpm_low
    if bpm_high:
        params["bpm-high"] = bpm_high
    url = f"https://www.beatport.com/genre/{genre_slug}/{genre_id}/tracks?{urllib.parse.urlencode(params)}"
    html = fetch_url(url)
    return _parse_bp_next_data(html) if html else []


def _parse_bp_next_data(html):
    m = re.search(r'<script[^>]*id="__NEXT_DATA__"[^>]*>(.*?)</script>', html, re.S)
    if not m:
        return []
    try:
        data = json.loads(m.group(1))
    except:
        return []
    tracks = []
    for q in data.get("props", {}).get("pageProps", {}).get("dehydratedState", {}).get("queries", []):
        for t in q.get("state", {}).get("data", {}).get("tracks", {}).get("data", []):
            p = _parse_bp_track(t)
            if p:
                tracks.append(p)
    return tracks


def _parse_bp_track(t):
    if not isinstance(t, dict):
        return None
    tid = t.get("track_id") or t.get("id")
    name = t.get("track_name") or t.get("name") or ""
    if not name:
        return None

    artists_raw = t.get("artists") or []
    artist_names = [a.get("artist_name") or a.get("name", "") for a in artists_raw if isinstance(a, dict)]

    raw_genre = t.get("genre") or t.get("sub_genre")
    genre_name, genre_id, genre_slug = "", None, ""
    if raw_genre:
        g = raw_genre[0] if isinstance(raw_genre, list) and raw_genre else raw_genre if isinstance(raw_genre, dict) else None
        if g:
            genre_name = g.get("genre_name") or g.get("name") or ""
            genre_id = g.get("genre_id") or g.get("id")
            genre_slug = g.get("slug") or ""

    key_name = t.get("key_name") or ""
    label_name = ""
    lb = t.get("label")
    if isinstance(lb, dict):
        label_name = lb.get("label_name") or lb.get("name") or ""

    img = ""
    rel = t.get("release") or {}
    if isinstance(rel, dict):
        img = rel.get("release_image_uri") or ""
    if not img:
        img = t.get("track_image_uri") or ""

    slug = t.get("slug") or re.sub(r'[^a-z0-9]+', '-', name.lower()).strip('-')

    return {
        "id": tid, "title": name, "mix": t.get("mix_name") or "",
        "artists": ", ".join(artist_names), "artist_list": artist_names,
        "genre": genre_name, "genre_id": genre_id, "genre_slug": genre_slug,
        "bpm": t.get("bpm"), "key": key_name, "camelot": normalize_key(key_name),
        "label": label_name, "artwork": img,
        "duration_ms": t.get("length") or t.get("length_ms"),
        "release_date": (t.get("release_date") or t.get("publish_date") or "")[:10],
        "sample_url": t.get("sample_url") or (f"https://geo-samples.beatport.com/track/{t['guid']}.LOFI.mp3" if t.get("guid") else ""),
        "url": f"https://www.beatport.com/track/{slug}/{tid}" if tid else "",
        "platform": "beatport",
    }


# ═══════════════════════════════════════
#  SOUNDCLOUD SCRAPER
# ═══════════════════════════════════════

_sc_client_id = None
_sc_client_id_ts = 0


def get_sc_client_id():
    global _sc_client_id, _sc_client_id_ts
    if _sc_client_id and time.time() - _sc_client_id_ts < 3600:
        return _sc_client_id
    print("  [SC] Scraping client_id...")
    html = fetch_url("https://soundcloud.com")
    if not html:
        return None
    scripts = re.findall(r'src="(https://a-v2\.sndcdn\.com/assets/[^"]+\.js)"', html)
    for s in scripts[-6:]:
        js = fetch_url(s)
        if js:
            m = re.search(r'client_id\s*[:=]\s*"([a-zA-Z0-9]{20,})"', js)
            if m:
                _sc_client_id = m.group(1)
                _sc_client_id_ts = time.time()
                print(f"  [SC] Got client_id: {_sc_client_id[:12]}...")
                return _sc_client_id
    print("  [SC] Could not find client_id")
    return None


def search_soundcloud(query, limit=50):
    cid = get_sc_client_id()
    if not cid:
        return []
    url = f"https://api-v2.soundcloud.com/search/tracks?q={urllib.parse.quote(query)}&client_id={cid}&limit={limit}"
    data = fetch_json(url)
    if not data:
        return []
    return [_parse_sc_track(t) for t in data.get("collection", []) if isinstance(t, dict)]


def _parse_sc_track(t):
    user = t.get("user") or {}
    artwork = (t.get("artwork_url") or "").replace("-large", "-t300x300")
    if not artwork:
        artwork = (user.get("avatar_url") or "").replace("-large", "-t300x300")

    # Find progressive stream transcoding URL
    stream_url = ""
    for tc in (t.get("media") or {}).get("transcodings") or []:
        fmt = tc.get("format") or {}
        if fmt.get("protocol") == "progressive":
            stream_url = tc.get("url") or ""
            break
    # Fallback to any transcoding
    if not stream_url:
        for tc in (t.get("media") or {}).get("transcodings") or []:
            stream_url = tc.get("url") or ""
            if stream_url:
                break

    return {
        "id": f"sc-{t.get('id', '')}",
        "title": t.get("title") or "",
        "mix": "",
        "artists": user.get("username") or "",
        "artist_list": [user.get("username") or ""],
        "genre": t.get("genre") or "",
        "tags": t.get("tag_list") or "",
        "bpm": None, "key": None, "camelot": None,
        "label": t.get("label_name") or "",
        "artwork": artwork,
        "duration_ms": t.get("duration"),
        "release_date": (t.get("release_date") or t.get("display_date") or t.get("created_at") or "")[:10],
        "sample_url": "",  # resolved on demand via /api/sc-stream
        "_transcoding_url": stream_url,
        "url": t.get("permalink_url") or "",
        "platform": "soundcloud",
    }


def resolve_sc_stream(transcoding_url):
    """Resolve a SoundCloud transcoding URL to an actual stream URL."""
    cid = get_sc_client_id()
    if not cid or not transcoding_url:
        return None
    url = f"{transcoding_url}?client_id={cid}"
    data = fetch_json(url)
    return data.get("url") if data else None


# ═══════════════════════════════════════
#  BANDCAMP SCRAPER
# ═══════════════════════════════════════

def search_bandcamp(query, limit=50):
    data = post_json(
        "https://bandcamp.com/api/bcsearch_public_api/1/autocomplete_elastic",
        {"search_text": query, "search_filter": "t", "full_page": True, "fan_id": None}
    )
    if not data:
        return []
    results = data.get("auto", {}).get("results", [])
    return [_parse_bc_result(r) for r in results[:limit] if r.get("type") == "t"]


def _parse_bc_result(r):
    img = r.get("img") or ""
    # Bandcamp image IDs: append _2 for 350px, _3 for 100px, _10 for 1200px
    if img and "_" not in img.split("/")[-1].split(".")[0]:
        img = img  # already has size suffix

    return {
        "id": f"bc-{r.get('id', '')}",
        "title": r.get("name") or "",
        "mix": "",
        "artists": r.get("band_name") or "",
        "artist_list": [r.get("band_name") or ""],
        "genre": "",  # not in search results
        "tags": "",
        "bpm": None, "key": None, "camelot": None,
        "label": "",
        "artwork": img,
        "duration_ms": None,
        "release_date": "",
        "sample_url": "",  # resolved on demand via /api/bc-preview
        "url": r.get("item_url_path") or "",
        "album": r.get("album_name") or "",
        "platform": "bandcamp",
    }


def resolve_bc_preview(track_url):
    """Fetch a Bandcamp track page and extract preview MP3 URL + release date."""
    html = fetch_url(track_url)
    if not html:
        return None, None
    stream_url = None
    release_date = None

    # Try data-tralbum attribute
    m = re.search(r'data-tralbum="([^"]+)"', html)
    if m:
        try:
            data = json.loads(html_module.unescape(m.group(1)))
            tracks = data.get("trackinfo") or []
            if tracks:
                f = tracks[0].get("file") or {}
                stream_url = f.get("mp3-128") or ""
            # Release date from album/track info
            rd = data.get("current", {}).get("release_date") or ""
            if rd:
                # Format: "29 Sep 2023 00:00:00 GMT" → extract year
                release_date = rd
        except:
            pass

    # Fallback: try trackinfo JS variable
    if not stream_url:
        m2 = re.search(r'trackinfo\s*:\s*(\[.*?\])\s*,', html, re.S)
        if m2:
            try:
                tracks = json.loads(m2.group(1))
                if tracks:
                    f = tracks[0].get("file") or {}
                    stream_url = f.get("mp3-128") or ""
            except:
                pass

    # Extract release date from page text: "released September 29, 2023" or "released October 4, 2024"
    if not release_date:
        dm = re.search(r'released\s+(\w+\s+\d{1,2},\s+\d{4})', html)
        if dm:
            release_date = dm.group(1)

    # Normalize release_date to YYYY-MM-DD
    if release_date:
        # Try parsing "29 Sep 2023 ..." or "September 29, 2023"
        for fmt in ["%d %b %Y %H:%M:%S %Z", "%d %b %Y", "%B %d, %Y"]:
            try:
                from datetime import datetime
                dt = datetime.strptime(release_date.strip().split(" GMT")[0], fmt)
                release_date = dt.strftime("%Y-%m-%d")
                break
            except:
                continue

    return stream_url, release_date


# ═══════════════════════════════════════
#  METADATA EXTRACTION FROM URLs
# ═══════════════════════════════════════

def extract_metadata(url):
    url = url.strip()
    if "beatport.com" in url:
        m = re.search(r'/track/[^/]+/(\d+)', url)
        if m:
            html = fetch_url(url)
            if html:
                tracks = _parse_bp_next_data(html)
                if tracks:
                    return tracks[0]
        return {"title": url, "artists": "", "source": "beatport"}
    elif "spotify.com" in url:
        oembed = f"https://open.spotify.com/oembed?url={urllib.parse.quote(url, safe='')}"
        data = fetch_json(oembed)
        if data:
            title = data.get("title", "")
            parts = title.split(" by ", 1) if " by " in title else [title, ""]
            return {"title": parts[0].strip(), "artists": parts[1].strip() if len(parts) > 1 else "", "source": "spotify"}
    elif "soundcloud.com" in url:
        oembed = f"https://soundcloud.com/oembed?url={urllib.parse.quote(url, safe='')}&format=json"
        data = fetch_json(oembed)
        if data:
            title = data.get("title", "")
            author = data.get("author_name", "")
            if " - " in title:
                parts = title.split(" - ", 1)
                return {"title": parts[1].strip(), "artists": parts[0].strip(), "source": "soundcloud"}
            return {"title": title, "artists": author, "source": "soundcloud"}
    elif "youtube.com" in url or "youtu.be" in url:
        oembed = f"https://www.youtube.com/oembed?url={urllib.parse.quote(url, safe='')}&format=json"
        data = fetch_json(oembed)
        if data:
            title = data.get("title", "")
            author = data.get("author_name", "")
            clean = re.sub(r'\s*[\(\[](official|lyric|music|audio|video|visuali|hd|hq|4k).*?[\)\]]', '', title, flags=re.I).strip(' -|')
            if " - " in clean:
                parts = clean.split(" - ", 1)
                return {"title": parts[1].strip(), "artists": parts[0].strip(), "source": "youtube"}
            return {"title": clean, "artists": author, "source": "youtube"}
    elif "bandcamp.com" in url:
        return {"title": url.split("/")[-1].replace("-", " "), "artists": "", "source": "bandcamp"}
    return {"title": url, "artists": "", "source": "text"}


# ═══════════════════════════════════════
#  FIND SIMILAR — per platform
# ═══════════════════════════════════════

def find_similar_beatport(source, count=50):
    all_tracks = []
    seen = set()
    src_id = source.get("id")
    if src_id:
        seen.add(src_id)

    # Enrich source from Beatport if needed
    if not source.get("bpm") and (source.get("artists") or source.get("title")):
        q = f"{source.get('artists', '')} {source.get('title', '')}".strip()
        if q:
            results = scrape_beatport_search(q)
            if results:
                source = {**source, **{k: v for k, v in results[0].items() if v}}
                seen.add(results[0].get("id"))
                for t in results[1:]:
                    if t.get("id") and t["id"] not in seen:
                        seen.add(t["id"])
                        all_tracks.append(t)

    # Search strategies
    for query in _build_queries(source):
        for t in scrape_beatport_search(query):
            if t.get("id") and t["id"] not in seen:
                seen.add(t["id"])
                all_tracks.append(t)

    # Genre browse with BPM filter
    if source.get("genre_slug") and source.get("genre_id") and source.get("bpm"):
        bpm = source["bpm"]
        for t in scrape_beatport_genre(source["genre_slug"], source["genre_id"], bpm - 5, bpm + 5):
            if t.get("id") and t["id"] not in seen:
                seen.add(t["id"])
                all_tracks.append(t)

    for t in all_tracks:
        t["similarity"] = compute_similarity_beatport(source, t)
    all_tracks.sort(key=lambda x: x["similarity"], reverse=True)
    return all_tracks[:count], source


def find_similar_soundcloud(source, count=50):
    all_tracks = []
    seen = set()

    for query in _build_queries(source):
        for t in search_soundcloud(query, limit=50):
            if t["id"] not in seen:
                seen.add(t["id"])
                all_tracks.append(t)

    for t in all_tracks:
        t["similarity"] = compute_similarity_text(source, t)
    all_tracks.sort(key=lambda x: x["similarity"], reverse=True)
    return all_tracks[:count]


def find_similar_bandcamp(source, count=50):
    all_tracks = []
    seen = set()

    for query in _build_queries(source):
        for t in search_bandcamp(query, limit=50):
            if t["id"] not in seen:
                seen.add(t["id"])
                all_tracks.append(t)

    for t in all_tracks:
        t["similarity"] = compute_similarity_text(source, t)
    all_tracks.sort(key=lambda x: x["similarity"], reverse=True)
    return all_tracks[:count]


def _build_queries(source):
    """Build search queries from source metadata."""
    queries = []
    artists = source.get("artists", "")
    title = source.get("title", "")

    # Full artist + title
    full = f"{artists} {title}".strip()
    if full:
        queries.append(full)

    # Artist only
    if artists:
        first_artist = artists.split(",")[0].strip()
        queries.append(first_artist)

    # Genre
    if source.get("genre"):
        queries.append(source["genre"])

    # Label
    if source.get("label"):
        queries.append(source["label"])

    return queries


def find_similar_all(source_meta, count=50):
    """Run all three platform searches in parallel."""
    results = {}
    enriched_source = source_meta

    with ThreadPoolExecutor(max_workers=3) as pool:
        futures = {
            pool.submit(find_similar_beatport, dict(source_meta), count): "beatport",
            pool.submit(find_similar_soundcloud, dict(source_meta), count): "soundcloud",
            pool.submit(find_similar_bandcamp, dict(source_meta), count): "bandcamp",
        }
        for f in as_completed(futures):
            platform = futures[f]
            try:
                result = f.result()
                if platform == "beatport":
                    tracks, enriched_source = result
                    results[platform] = {"tracks": tracks, "count": len(tracks)}
                else:
                    results[platform] = {"tracks": result, "count": len(result)}
            except Exception as e:
                print(f"  [{platform.upper()} ERROR] {e}")
                results[platform] = {"tracks": [], "count": 0, "error": str(e)}

    return results, enriched_source


# ═══════════════════════════════════════
#  HTTP SERVER
# ═══════════════════════════════════════

class Handler(http.server.SimpleHTTPRequestHandler):

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        params = dict(urllib.parse.parse_qsl(parsed.query))

        if path == "/api/search":
            self._handle_search(params)
        elif path == "/api/sc-stream":
            self._handle_sc_stream(params)
        elif path == "/api/bc-preview":
            self._handle_bc_preview(params)
        elif path == "/api/status":
            self._json({"ok": True})
        elif path == "/" or path == "/index.html":
            self._serve_file("index.html")
        else:
            super().do_GET()

    def _handle_search(self, params):
        url = params.get("url", "").strip()
        if not url:
            return self._json({"error": "Missing 'url' parameter"}, 400)
        print(f"\n[SEARCH] {url}")
        meta = extract_metadata(url)
        if not meta:
            return self._json({"error": "Could not extract metadata"}, 400)
        print(f"  Extracted: {meta.get('artists', '?')} - {meta.get('title', '?')}")
        results, enriched = find_similar_all(meta, count=50)
        self._json({"source": enriched, **results})

    def _handle_sc_stream(self, params):
        url = params.get("url", "").strip()
        if not url:
            return self._json({"error": "Missing url"}, 400)
        stream_url = resolve_sc_stream(url)
        self._json({"stream_url": stream_url or ""})

    def _handle_bc_preview(self, params):
        url = params.get("url", "").strip()
        if not url:
            return self._json({"error": "Missing url"}, 400)
        stream_url, release_date = resolve_bc_preview(url)
        self._json({"stream_url": stream_url or "", "release_date": release_date or ""})

    def _json(self, data, status=200):
        body = json.dumps(data).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Content-Length", len(body))
        self.end_headers()
        self.wfile.write(body)

    def _serve_file(self, name):
        fp = os.path.join(os.path.dirname(os.path.abspath(__file__)), name)
        if os.path.exists(fp):
            with open(fp, "rb") as f:
                c = f.read()
            self.send_response(200)
            self.send_header("Content-Type", "text/html")
            self.send_header("Content-Length", len(c))
            self.end_headers()
            self.wfile.write(c)
        else:
            self.send_response(404)
            self.end_headers()

    def log_message(self, fmt, *args):
        if "/api/" in str(args[0] if args else ""):
            super().log_message(fmt, *args)


if __name__ == "__main__":
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    print(f"🎵 Similar Track Finder — Beatport + SoundCloud + Bandcamp")
    print(f"   http://localhost:{PORT}")
    print(f"   Press Ctrl+C to stop\n")
    server = http.server.HTTPServer(("", PORT), Handler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n[SERVER] Stopped")
        server.server_close()
