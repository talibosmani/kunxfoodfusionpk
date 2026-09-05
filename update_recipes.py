#!/usr/bin/env python3
"""
update_recipes.py — self-contained pipeline for Bhook Lagi hai.

Run it whenever you want to pull in new videos from KunFoods and FoodfusionPk,
parse their ingredients, scrape foodfusion.com's written recipes for anything
that needs it, and refresh index.html — all without going through Claude.

    python3 update_recipes.py

Safe to re-run. Every stage checkpoints its progress to update_state/*.json,
so if it gets interrupted (network hiccup, Ctrl+C, bit.ly rate limiting,
whatever) just run it again — it picks up where it left off instead of
starting over. Nothing is ever re-fetched once it succeeds.

What it does, in order:
  1. List current videos on both channels (yt-dlp --flat-playlist)
  2. Diff against what's already in index.html to find new videos only
  3. Merge same-dish videos across channels, classify cuisine/dessert/salad
  4. Fetch each new video's YouTube description (cookie-authenticated —
     see NOTE below on why this method and not another)
  5. Parse ingredients out of those descriptions (Urdu/English normalized)
  6. Follow any bit.ly "written recipe" links to foodfusion.com and scrape
     their cleaner structured ingredients + directions
  7. Merge everything into index.html and Merged_Recipes.csv

NOTE on the YouTube fetch method: plain yt-dlp requests eventually get an
IP-level "Sign in to confirm you're not a bot" bot-check under any real
volume. Two workarounds were tested — using yt-dlp's alternate `android`
player client, and authenticating as a logged-in user via browser cookies.
Only the cookie method held up at scale with zero bot-checks across 1,400+
consecutive requests, so that's what this script uses by default. It needs
Chrome installed and logged into youtube.com. If cookie export fails for
any reason, it automatically falls back to the android-client method,
which is less reliable under heavy load but doesn't require login.

NOTE on foodfusion.com scraping: their recipe pages have used two different
HTML templates during this project (an older <ul class="am-ing"> list, and
a newer plain <p> paragraph format) — sometimes inconsistently, mid-migration.
This script's parser recognizes both. If they change it again, ingredient
scraping for new recipes may silently stop finding anything; check a sample
page by hand if the "written-recipe scraped" count looks off.
"""

import argparse
import concurrent.futures
import html as html_module
import json
import os
import random
import re
import shutil
import subprocess
import sys
import threading
import time

# ─────────────────────────────────────────────────────────────────────────
# Paths & constants
# ─────────────────────────────────────────────────────────────────────────

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
INDEX_HTML = os.path.join(SCRIPT_DIR, 'index.html')
MERGED_CSV = os.path.join(SCRIPT_DIR, 'Merged_Recipes.csv')
STATE_DIR = os.path.join(SCRIPT_DIR, 'update_state')
COOKIES_FILE = os.path.join(STATE_DIR, 'youtube_cookies.txt')

KUNFOODS_URL = 'https://www.youtube.com/@KunFoods/videos'
FOODFUSION_URL = 'https://www.youtube.com/@FoodfusionPk/videos'

DESC_FETCH_WORKERS = 8
FF_SCRAPE_WORKERS = 8
MAX_RETRIES = 6


def ensure_state_dir():
    os.makedirs(STATE_DIR, exist_ok=True)


def load_checkpoint(name):
    path = os.path.join(STATE_DIR, name)
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    return {}


def save_checkpoint(name, data):
    path = os.path.join(STATE_DIR, name)
    tmp = path + '.tmp'
    with open(tmp, 'w') as f:
        json.dump(data, f)
    os.replace(tmp, path)


# ─────────────────────────────────────────────────────────────────────────
# Stage 1: list channel videos
# ─────────────────────────────────────────────────────────────────────────

def fetch_channel_videos(label, channel_url):
    print(f"[1/7] Listing videos on {label}...")
    result = subprocess.run(
        ['yt-dlp', '--flat-playlist', '--print', '%(id)s\t%(title)s', channel_url],
        capture_output=True, text=True, timeout=180
    )
    videos = []
    for line in result.stdout.strip().split('\n'):
        if '\t' not in line:
            continue
        vid, title = line.split('\t', 1)
        videos.append({'id': vid.strip(), 'title': title.strip()})
    print(f"      Found {len(videos)} videos on {label}")
    return videos


# ─────────────────────────────────────────────────────────────────────────
# Stage 2: classification heuristics (cuisine / dessert / salad)
# ─────────────────────────────────────────────────────────────────────────

NON_RECIPE_RE = re.compile(
    r'\b(vlog|subscribers?|celebration|giveaway|unboxing|q\s?&\s?a|thank you|tour|haul|expo)\b',
    re.IGNORECASE)
CHINESE_RE = re.compile(
    r'\b(chinese|wok|manchurian|schezwan|szechwan|hakka|dim ?sum|chow ?mein|spring ?roll|fried rice|dumplings?)\b',
    re.IGNORECASE)
JAPANESE_RE = re.compile(
    r'\b(japanese|sushi|ramen|teriyaki|tempura|miso|udon|yakitori)\b', re.IGNORECASE)
ARABIC_RE = re.compile(
    r'\b(arabic|mediterranean|shawarma|hummus|falafel|kabsa|tabbouleh|fattoush|kunafa|baklava|mandi|harissa|mutabbaq)\b',
    re.IGNORECASE)
CONTINENTAL_RE = re.compile(
    r'\b(pizza|pasta|burger|sandwich|steak|italian|mexican|lasagna|risotto|waffles?|pancakes?|tex[- ]?mex)\b',
    re.IGNORECASE)
DESSERT_RE = re.compile(
    r'\bkheer\b|\bhalwa\b|\bhalva\b|\bbarfi\b|\bburfi\b|\bladdu\b|\bladoo\b|\bgulab jamun\b|\bras\s*malai\b|'
    r'\bjalebi\b|\bkulfi\b|\bfalooda\b|\bsheer\s*khurma\b|\bzarda\b|\bsev[ai]y[ai]n\b|\bfirni\b|\bphirni\b|'
    r'\brabri\b|\bmalpua\b|\bgujiya\b|\bshahi\s*tukr[ae]?y?\b|\bmithai\b|\bpeda\b|\bbaklava\b|\bkunafa\b|'
    r'\bcake\b|\bcupcake\b|\bbrownies?\b|\bcookies?\b|\bpudding\b|\bmousse\b|\btrifle\b|\bice\s*cream\b|'
    r'\bdo[nu]+ghn?uts?\b|\bcheesecake\b|\bmuffins?\b|\btiramisu\b|\bfudge\b|\bcustard\b|\bmacarons?\b|'
    r'\becl[ae]irs?\b|\bcinnamon\s*rolls?\b|\btruffles?\b|\btoffee\b|\bcaramel\b|\bmarshmallow\b|\bmeringue\b|'
    r'\bparfait\b|\bcobbler\b|\bcrumble\b|\bcannolis?\b|\bchurros?\b|\bfondant\b|\bicing\b|\bfruit\s*chaat\b|'
    r'\bfruit\s*salad\b|\btart\b|\bpies?\b',
    re.IGNORECASE)
DESSERT_EXCLUDE_RE = re.compile(
    r'\bchicken\s*pie\b|\bmeat\s*pie\b|\bpot\s*pie\b|\bfish\s*pie\b|\bpotato\s*pancakes?\b|'
    r'\bpizza\s*pie\b|\bchicken\s*bread\s*(sandwich\s*)?cake\b|\bchicken\s*candy\b|\bchicken\s*do[nu]+ghn?uts?\b|'
    r'\bchicken\s*popsicles?\b|\b(veg\s*&?\s*)?chicken\s*pies?\b|\broast\s*chicken.*tart\b|\btoffee\s*kabab\b|'
    r'\bvegetable\s*pancakes?\b|\bachari\s*waffles?\b',
    re.IGNORECASE)
SALAD_RE = re.compile(r'\bsalads?\b|\bcoleslaw\b', re.IGNORECASE)


def classify_cuisine(title):
    if NON_RECIPE_RE.search(title):
        return 'Non-Recipe/Vlog'
    if CHINESE_RE.search(title):
        return 'Chinese'
    if JAPANESE_RE.search(title):
        return 'Japanese'
    if ARABIC_RE.search(title):
        return 'Arabic/Mediterranean'
    if CONTINENTAL_RE.search(title):
        return 'Continental'
    return 'Indian/Pakistani'


def classify_dessert(title):
    return bool(DESSERT_RE.search(title)) and not DESSERT_EXCLUDE_RE.search(title)


def classify_salad(title):
    return bool(SALAD_RE.search(title))


def normalize_title_key(title):
    key = title.lower().strip()
    key = re.sub(r'[^a-z0-9\s]', '', key)
    key = re.sub(r'\s+', ' ', key).strip()
    return key


# ─────────────────────────────────────────────────────────────────────────
# Stage 3: YouTube description fetching
# ─────────────────────────────────────────────────────────────────────────

def setup_youtube_cookies():
    """Export Chrome's YouTube cookies to a static file. Returns True if it works."""
    print("[3/7] Setting up YouTube authentication (cookie export from Chrome)...")
    try:
        r = subprocess.run(
            ['yt-dlp', '--cookies-from-browser', 'chrome', '--cookies', COOKIES_FILE,
             '--skip-download', '--print', 'ok', '--playlist-items', '1',
             'https://www.youtube.com/@KunFoods/videos'],
            capture_output=True, text=True, timeout=30
        )
        if os.path.exists(COOKIES_FILE) and os.path.getsize(COOKIES_FILE) > 0:
            print("      Cookie export succeeded — using authenticated requests (most reliable).")
            return True
    except Exception as e:
        print(f"      Cookie export failed: {e}")
    print("      Falling back to android-client method (works without login, less reliable at scale).")
    return False


def fetch_one_description(video_id, use_cookies):
    for attempt in range(MAX_RETRIES):
        try:
            if use_cookies:
                cmd = ['yt-dlp', '--cookies', COOKIES_FILE, '--skip-download',
                       '--ignore-no-formats-error', '--print', 'description',
                       f'https://www.youtube.com/watch?v={video_id}']
            else:
                cmd = ['yt-dlp', '--skip-download',
                       '--extractor-args', 'youtube:player_client=android',
                       '--print', 'description',
                       f'https://www.youtube.com/watch?v={video_id}']
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            desc = r.stdout.strip()
            if desc and len(desc) >= 20:
                return video_id, desc
            if 'not a bot' in r.stderr:
                time.sleep(random.uniform(3, 6))
        except Exception:
            pass
        time.sleep(random.uniform(0.5, 1.5))
    return video_id, None


def fetch_descriptions(video_ids, use_cookies):
    print(f"[4/7] Fetching {len(video_ids)} video descriptions...")
    checkpoint = load_checkpoint('descriptions.json')
    remaining = [v for v in video_ids if v not in checkpoint]
    if not remaining:
        print("      All descriptions already fetched.")
        return checkpoint

    print(f"      {len(video_ids) - len(remaining)} already done, {len(remaining)} remaining")
    count = 0
    lock = threading.Lock()
    with concurrent.futures.ThreadPoolExecutor(max_workers=DESC_FETCH_WORKERS) as executor:
        futures = {executor.submit(fetch_one_description, vid, use_cookies): vid for vid in remaining}
        for future in concurrent.futures.as_completed(futures):
            vid, desc = future.result()
            with lock:
                checkpoint[vid] = desc or ""
                count += 1
                if count % 25 == 0:
                    save_checkpoint('descriptions.json', checkpoint)
                    good = sum(1 for v in checkpoint.values() if v)
                    print(f"      {count}/{len(remaining)} done ({good} with content)")

    save_checkpoint('descriptions.json', checkpoint)
    good = sum(1 for vid in video_ids if checkpoint.get(vid))
    print(f"      Finished: {good}/{len(video_ids)} descriptions fetched")
    return checkpoint


# ─────────────────────────────────────────────────────────────────────────
# Stage 4: ingredient parsing (YouTube description text)
# ─────────────────────────────────────────────────────────────────────────

STOP_MARKERS_RE = re.compile(
    r'\bdirections?\s*:|\bmethod\s*:|\binstructions?\s*:|\brecipe in urdu\b|\bajza\s*:|👇|'
    r'\bwritten recipe\b|\bfollow (me|us)\b|\bsubscribe\b|\bvisit our website\b|'
    r'\bfacebook\.com\b|\binstagram\.com\b|welcome to', re.IGNORECASE)

UNIT_WORDS = (r'(cups?|tbs?p?s?|tsp?s?|gms?|gr?ams?|kgs?|kilograms?|ml|milliliters?|liters?|litres?|l\b|'
              r'pinch(es)?|to taste|as required|as needed|or to taste|medium|large|small|whole|pieces?|pcs?|'
              r'inch(es)?|cloves?|leaves?|slices?|cans?|packs?|packets?|bunche?s?|sprigs?|strips?|handfuls?)')
FRACTIONS = '½¼¾⅓⅔⅛⅜⅝⅞'

URDU_TO_EN = {
    'namak': 'salt', 'pyaz': 'onion', 'doodh': 'milk', 'zeera': 'cumin',
    'adrak': 'ginger', 'lehsan': 'garlic', 'lassan': 'garlic', 'dahi': 'yogurt',
    'haldi': 'turmeric', 'haldee': 'turmeric', 'dhania': 'coriander', 'dhaniya': 'coriander',
    'mirch': 'chili', 'mirchi': 'chili', 'elaichi': 'cardamom', 'ilaichi': 'cardamom',
    'darchini': 'cinnamon', 'dar': 'cinnamon', 'laung': 'clove', 'long': 'clove',
    'maida': 'flour', 'atta': 'wheat flour', 'ghee': 'ghee', 'makhan': 'butter',
    'pani': 'water', 'ande': 'egg', 'anda': 'egg', 'anday': 'egg', 'andy': 'egg',
    'murgh': 'chicken', 'murghi': 'chicken', 'gosht': 'meat', 'chawal': 'rice',
    'shakar': 'sugar', 'cheeni': 'sugar', 'til': 'sesame', 'kaju': 'cashew',
    'badam': 'almond', 'kishmish': 'raisin', 'imli': 'tamarind', 'sirka': 'vinegar',
    'hari': 'green', 'harey': 'green', 'hara': 'green', 'lal': 'red', 'laal': 'red',
    'kali': 'black', 'kala': 'black', 'kaali': 'black', 'safed': 'white',
    'safaid': 'white', 'peeli': 'yellow', 'peela': 'yellow',
    'namkeen': 'salted', 'meetha': 'sweet', 'khatta': 'sour',
    'aloo': 'potato', 'aalo': 'potato', 'aam': 'mango', 'tamatar': 'tomato', 'baingan': 'eggplant', 'bhindi': 'okra',
    'palak': 'spinach', 'gajar': 'carrot', 'mattar': 'peas', 'matar': 'peas',
    'shimla': 'bell', 'mirchein': 'peppers', 'karahi': 'wok',
    'sabut': 'whole', 'pisi': 'ground', 'pisa': 'ground', 'crushed': 'crushed',
    'roghan': 'oil', 'tel': 'oil', 'malai': 'cream', 'khoya': 'khoya',
    'besan': 'gram flour', 'baisan': 'gram flour', 'suji': 'semolina', 'sooji': 'semolina',
    'khameer': 'yeast', 'baking': 'baking', 'podina': 'mint',
    'saunf': 'fennel seed', 'ajwain': 'carom seed', 'khopra': 'desiccated coconut',
    'koyla': 'charcoal', 'jaifil': 'nutmeg', 'kheera': 'cucumber',
    'zardi': 'yolk', 'safedi': 'white', 'papita': 'papaya', 'kacha': 'raw',
    'qeema': 'mince', 'keema': 'mince', 'tatri': 'citric acid', 'yakhni': 'stock',
    'ki': '', 'ka': '', 'ke': '',
}

PHRASE_FIXES = [
    (r'\bkali mirch\b', 'black pepper'), (r'\bkaali mirch\b', 'black pepper'),
    (r'\bsafed mirch\b', 'white pepper'), (r'\bshimla mirch\b', 'bell pepper'),
    (r'\bpeeli mirch\b', 'yellow pepper'), (r'\btez pa+t+a?\b', 'bay leaf'),
    (r'\bbadiyan ka phool\b', 'star anise'), (r'\bzarda ka rang\b', 'food coloring'),
    (r'\bkasuri methi\b', 'dried fenugreek leaf'), (r'\bolper.?s\b', ''),
]

PREP_WORDS = (r'\b(chopped|sliced|diced|minced|crushed|grated|julienned?|julienne|boiled|roasted|fresh|dried|'
              r'ground|sifted|beaten|whisked|cubed|cubes?|finely|thinly|boneless|skinless|cooked|raw|ripe|'
              r'unsalted|softened|melted|cold|room temperature|optional|garnish(ing)?|for garnish(ing)?|'
              r'for frying|for smoke|for greasing|for serving|for taste|as required|approx\.?|chunks?|halved|'
              r'quartered|peeled|deveined|shredded|toasted|blanched|deseeded|whole)\b')

CANONICAL_MERGE = {
    'himalayan pink salt': 'salt', 'iodized himalayan pink salt': 'salt', 'iodized salt': 'salt',
    'cooking oil for frying': 'cooking oil', 'oil for frying': 'cooking oil', 'oil': 'cooking oil',
    'olper cream': 'cream', 'olper milk': 'milk', 'olper cheddar cheese': 'cheddar cheese',
    'corn flour': 'cornflour', 'green chily': 'green chili',
    'hot water': 'water', 'warm water': 'water', 'boiling water': 'water', 'cold water': 'water',
    'garam masala': 'garam masala powder', 'chicken cube': 'chicken powder',
    'sugar powdered': 'icing sugar', 'bareek sugar': 'sugar', 'castor sugar': 'sugar', 'caster sugar': 'sugar',
}


def extract_ingredient_section(desc):
    m = re.search(r'ingredients\s*:?', desc, re.IGNORECASE)
    if not m:
        return None
    text = desc[m.end():]
    stop = STOP_MARKERS_RE.search(text)
    if stop:
        text = text[:stop.start()]
    return text.strip()


def clean_name(line):
    line = line.strip()
    line = re.sub(r'[​‌‍﻿⁠]', '', line)
    line = re.sub(r'^[-•*]+\s*', '', line)
    if not line:
        return None
    cut_pattern = r'[\d' + FRACTIONS + ']'
    parts = re.split(cut_pattern, line, maxsplit=1)
    name = parts[0].strip()
    name = re.sub(r'\(.*?\)', '', name).strip()
    name = re.sub(r'\b' + UNIT_WORDS + r'\b.*$', '', name, flags=re.IGNORECASE).strip()
    name = re.sub(r'[-–—:]+$', '', name).strip()
    name = re.sub(r'\s+(of|for|or|with|and|the|a|an)$', '', name, flags=re.IGNORECASE).strip()
    name = re.sub(r'\s+', ' ', name)
    if not name or len(name) < 2 or len(name) > 40:
        return None
    if name.lower() in ('ingredients', 'ajza', 'directions', 'method'):
        return None
    return name


def parse_ingredients_from_description(desc):
    section = extract_ingredient_section(desc)
    if not section:
        return []
    items = []
    for raw_line in section.split('\n'):
        raw_line = raw_line.strip()
        if not raw_line:
            continue
        if re.match(r'^[A-Za-z ]{3,30}[-:]\s*$', raw_line) and not re.search(r'\d', raw_line):
            continue
        name = clean_name(raw_line)
        if name:
            items.append(name)
    seen = set()
    result = []
    for item in items:
        key = item.lower()
        if key not in seen:
            seen.add(key)
            result.append(item)
    return result[:25]


def translate_and_normalize(name):
    key = name.lower().strip()
    key = re.sub(r'[^a-z\s]', ' ', key)
    for pattern, repl in PHRASE_FIXES:
        key = re.sub(pattern, repl, key, flags=re.IGNORECASE)
    words = key.split()
    translated = [URDU_TO_EN.get(w, w) for w in words]
    key = ' '.join(translated)
    key = re.sub(r'\s+', ' ', key).strip()
    key = re.sub(PREP_WORDS, '', key, flags=re.IGNORECASE)
    key = re.sub(r'\s+', ' ', key).strip()
    words = key.split()
    singular_words = []
    for w in words:
        if w.endswith('ies') and len(w) > 4:
            w = w[:-3] + 'y'
        elif w.endswith('es') and len(w) > 4 and w.endswith(('shes', 'ches', 'xes', 'ses')):
            w = w[:-2]
        elif w.endswith('s') and len(w) > 3 and not w.endswith('ss'):
            w = w[:-1]
        singular_words.append(w)
    key = ' '.join(singular_words).strip()
    return CANONICAL_MERGE.get(key, key)


def clean_ingredients(raw_names):
    """raw_names: list of plain ingredient-line strings (already quantity-stripped or not)."""
    seen_keys = set()
    paired = []
    for name in raw_names:
        cleaned = clean_name(name) if any(c.isdigit() or c in FRACTIONS for c in name) else name.strip()
        if not cleaned:
            continue
        key = translate_and_normalize(cleaned)
        if key and len(key) >= 2 and key not in seen_keys:
            seen_keys.add(key)
            paired.append({"name": cleaned, "key": key})
    return paired, seen_keys


# ─────────────────────────────────────────────────────────────────────────
# Stage 5: foodfusion.com scraping (bit.ly links)
# ─────────────────────────────────────────────────────────────────────────

def _clean_text(raw):
    text = re.sub(r'<[^>]+>', '', raw).strip()
    text = html_module.unescape(text)
    text = text.replace('\xa0', ' ').strip()
    text = re.sub(r'\s+', ' ', text).strip()
    return text


def _parse_old_ff_format(block):
    ing_section_match = re.search(r'Ingredients:.*?(?=<h2[^>]*>Directions|$)', block, re.DOTALL | re.IGNORECASE)
    ingredients = []
    if ing_section_match:
        parts = re.split(r'(<h4>.*?</h4>)', ing_section_match.group(0))
        current_section = None
        for part in parts:
            h4_match = re.match(r'<h4>(.*?)</h4>', part)
            if h4_match:
                current_section = _clean_text(h4_match.group(1))
                continue
            for li in re.findall(r'<li[^>]*>(.*?)</li>', part, re.DOTALL):
                text = _clean_text(li)
                if text:
                    ingredients.append({"name": text, "section": current_section})

    dir_section_match = re.search(r'Directions:.*', block, re.DOTALL | re.IGNORECASE)
    directions = ""
    if dir_section_match:
        dir_section = dir_section_match.group(0)
        dir_section = re.split(r'<h2', dir_section)[0] if dir_section.count('<h2') else dir_section
        clean_paras = []
        for p in re.findall(r'<p>(.*?)</p>', dir_section, re.DOTALL):
            text = _clean_text(p)
            if text and 'Directions' not in text:
                clean_paras.append(text)
        directions = '\n\n'.join(clean_paras)

    return ingredients, directions


def _parse_new_ff_format(block):
    m = re.search(r'<p>\s*Ingredients:?\s*</p>(.*?)(?=<p>\s*Direction:?s?\s*</p>|$)', block, re.DOTALL | re.IGNORECASE)
    ingredients = []
    if m:
        current_section = None
        for p in re.findall(r'<p>(.*?)</p>', m.group(1), re.DOTALL):
            text = _clean_text(p)
            if not text:
                continue
            if text.startswith('-'):
                name = text.lstrip('-').strip()
                if name:
                    ingredients.append({"name": name, "section": current_section})
            else:
                current_section = text.rstrip(':').strip()

    d = re.search(r'<p>\s*Direction:?s?\s*</p>(.*?)(?=<div class="urdu-detail-ff"|<h2|$)', block, re.DOTALL | re.IGNORECASE)
    directions = ""
    if d:
        clean_paras = []
        for p in re.findall(r'<p>(.*?)</p>', d.group(1), re.DOTALL):
            text = _clean_text(p)
            if text:
                clean_paras.append(text.lstrip('-').strip())
        directions = '\n\n'.join(clean_paras)

    return ingredients, directions


def parse_foodfusion_page(page_html):
    """Handles both the old <ul class="am-ing"> template and the newer plain <p> template."""
    block_match = re.search(
        r'<div class="english-detail-ff">(.*?)(?:<div class="urdu-detail-ff"|<div id="related|$)',
        page_html, re.DOTALL)
    if not block_match:
        return None, None
    block = block_match.group(1)

    if 'am-ing' in page_html:
        ingredients, directions = _parse_old_ff_format(block)
    else:
        ingredients, directions = _parse_new_ff_format(block)

    if not ingredients:
        return None, None
    return ingredients, directions


WRITTEN_RECIPE_SHORTENER_RE = re.compile(r'https?://(?:bit\.ly|shorturl\.at|ln\.run|tinyurl\.com)/\S+')
FOOTER_MARKERS_RE = re.compile(
    r'(visit our (website|store)|download ios|facebook:|instagram:|twitter:|also follow|welcome to|'
    r'follow me on instagram|for any inquiry|subscribe)', re.IGNORECASE)
LABELED_LINK_RE = re.compile(r'^\s*(?:\d{1,2}:\d{2}(?::\d{2})?\s+)?(.+?):\s*(https?://\S+)\s*$', re.MULTILINE)


def extract_written_recipe_links(description):
    """Returns (single_url, None) or (None, [(label, url), ...]) or (None, None)."""
    links = list(set(u.rstrip('.,;)') for u in WRITTEN_RECIPE_SHORTENER_RE.findall(description)))
    if not links:
        return None, None
    if len(links) == 1:
        return links[0], None

    m = re.search(r'written\s*recipes?\s*:?', description, re.IGNORECASE)
    if not m:
        return None, None
    section = description[m.end():]
    stop = FOOTER_MARKERS_RE.search(section)
    if stop:
        section = section[:stop.start()]
    labeled = []
    for label, url in LABELED_LINK_RE.findall(section):
        label = label.strip()
        if re.match(r'^more\s.*recipes?$', label, re.IGNORECASE) or not label or len(label) > 80:
            continue
        labeled.append((label, url.rstrip('.,;)')))
    if len(labeled) >= 2:
        return None, labeled
    return None, None


def fetch_and_parse_ff_page(url):
    for attempt in range(MAX_RETRIES):
        try:
            r = subprocess.run(
                ['curl', '-s', '-L', '-A', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)', '--max-time', '15', url],
                capture_output=True, text=True, timeout=20
            )
            ingredients, directions = parse_foodfusion_page(r.stdout)
            if ingredients:
                return url, {"ingredients": ingredients, "directions": directions, "source_url": url}
        except Exception:
            pass
        time.sleep(random.uniform(0.3, 0.8))
    return url, None


def scrape_written_recipes(url_list):
    print(f"[6/7] Scraping {len(url_list)} written-recipe pages from foodfusion.com...")
    checkpoint = load_checkpoint('foodfusion_scraped.json')
    remaining = [u for u in url_list if u not in checkpoint]
    if not remaining:
        print("      Already scraped.")
        return checkpoint

    print(f"      {len(url_list) - len(remaining)} already done, {len(remaining)} remaining")
    count = 0
    lock = threading.Lock()
    with concurrent.futures.ThreadPoolExecutor(max_workers=FF_SCRAPE_WORKERS) as executor:
        futures = {executor.submit(fetch_and_parse_ff_page, u): u for u in remaining}
        for future in concurrent.futures.as_completed(futures):
            url, data = future.result()
            with lock:
                checkpoint[url] = data
                count += 1
                if count % 25 == 0:
                    save_checkpoint('foodfusion_scraped.json', checkpoint)
                    good = sum(1 for v in checkpoint.values() if v)
                    print(f"      {count}/{len(remaining)} done ({good} successful)")

    save_checkpoint('foodfusion_scraped.json', checkpoint)
    good = sum(1 for u in url_list if checkpoint.get(u))
    print(f"      Finished: {good}/{len(url_list)} written recipes scraped")
    return checkpoint


# ─────────────────────────────────────────────────────────────────────────
# Stage 6/7: merge into index.html + CSV
# ─────────────────────────────────────────────────────────────────────────

def load_existing_recipes():
    with open(INDEX_HTML) as f:
        html = f.read()
    start_marker = "const allRecipes = "
    start_idx = html.index(start_marker) + len(start_marker)
    end_idx = html.index(";\nconst topIngredients")
    recipes = json.loads(html[start_idx:end_idx])
    return html, recipes


def build_top_ingredients(recipes):
    from collections import Counter
    freq = Counter()
    for r in recipes:
        for key in r.get('ingredient_keys', []):
            freq[key] += 1
    return [{"key": k, "name": k.title(), "count": c} for k, c in freq.most_common(120)]


def write_recipes_to_html(html, recipes):
    start_marker = "const allRecipes = "
    start_idx = html.index(start_marker) + len(start_marker)
    end_idx = html.index(";\nconst topIngredients")
    html = html[:start_idx] + json.dumps(recipes) + html[end_idx:]

    top_ingredients = build_top_ingredients(recipes)
    ti_start_marker = "const topIngredients = "
    ti_start_idx = html.index(ti_start_marker) + len(ti_start_marker)
    ti_end_idx = html.index(";\nlet currentCuisine")
    html = html[:ti_start_idx] + json.dumps(top_ingredients) + html[ti_end_idx:]

    covered = sum(1 for r in recipes if r.get('ingredients') or r.get('sub_recipes'))
    html = re.sub(r'📝 <strong>\d+ with verified ingredients</strong>',
                  f'📝 <strong>{covered} with verified ingredients</strong>', html)
    html = re.sub(r'Loaded: <strong>[\d,]+ unique recipes</strong>',
                  f'Loaded: <strong>{len(recipes):,} unique recipes</strong>', html)

    with open(INDEX_HTML, 'w') as f:
        f.write(html)


def write_merged_csv(recipes):
    import csv
    with open(MERGED_CSV, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['Dish Name', 'Cuisine Type', 'Channels', 'KunFoods Video', 'KunFoods Link',
                          'FoodfusionPk Video', 'FoodfusionPk Link'])
        for r in recipes:
            writer.writerow([
                r['dish'], r['cuisine'], r['channels'],
                r['kunfoods_video'] or '-', r['kunfoods_link'] or '-',
                r['foodfusion_video'] or '-', r['foodfusion_link'] or '-',
            ])


# ─────────────────────────────────────────────────────────────────────────
# Main pipeline
# ─────────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--clean-state', action='store_true',
                         help='Wipe checkpoint files first (forces a full re-fetch of anything in progress)')
    args = parser.parse_args()

    ensure_state_dir()

    if args.clean_state and os.path.exists(STATE_DIR):
        shutil.rmtree(STATE_DIR)
        ensure_state_dir()
        print("Cleared update_state/ — starting fresh.\n")

    print("=" * 60)
    print("Bhook Lagi hai — recipe updater")
    print("=" * 60)

    if not os.path.exists(INDEX_HTML):
        print(f"ERROR: {INDEX_HTML} not found. Run this script from inside kunxfoodfusionpk/.")
        sys.exit(1)

    html, existing_recipes = load_existing_recipes()
    existing_ids = set()
    for r in existing_recipes:
        if r.get('kunfoods_id'):
            existing_ids.add(r['kunfoods_id'])
        if r.get('foodfusion_id'):
            existing_ids.add(r['foodfusion_id'])
    existing_titles = {normalize_title_key(r['dish']): r for r in existing_recipes}

    print(f"Currently have {len(existing_recipes)} recipes in index.html\n")

    # Stage 1
    kunfoods_videos = fetch_channel_videos('KunFoods', KUNFOODS_URL)
    foodfusion_videos = fetch_channel_videos('FoodfusionPk', FOODFUSION_URL)

    new_kunfoods = [v for v in kunfoods_videos if v['id'] not in existing_ids]
    new_foodfusion = [v for v in foodfusion_videos if v['id'] not in existing_ids]

    print(f"\n[2/7] New videos: {len(new_kunfoods)} on KunFoods, {len(new_foodfusion)} on FoodfusionPk")

    if not new_kunfoods and not new_foodfusion:
        print("\nNothing new — dataset is already up to date. Done.")
        return

    # Stage 2: merge new videos into recipe entries, matching same-dish titles across channels
    new_recipes_map = {}  # normalized title -> recipe dict
    # existing entries that gained a new link and still need a description fetch:
    # (entry, the specific newly-attached video id to fetch — NOT kunfoods_id-or-foodfusion_id,
    # since that fallback could resolve to the OLD side that we already know has no ingredients)
    enriched_existing = []
    for v in new_kunfoods:
        key = normalize_title_key(v['title'])
        if key in existing_titles:
            # matches an existing FoodfusionPk-only entry — attach KunFoods side to it
            entry = existing_titles[key]
            entry['kunfoods_video'] = v['title']
            entry['kunfoods_link'] = f"https://www.youtube.com/watch?v={v['id']}"
            entry['kunfoods_id'] = v['id']
            entry['channels'] = "2 channels"
            if not entry.get('ingredients') and not entry.get('sub_recipes'):
                enriched_existing.append((entry, v['id']))
            continue
        new_recipes_map[key] = {
            "dish": v['title'], "cuisine": classify_cuisine(v['title']), "channels": "1 channel",
            "kunfoods_video": v['title'], "kunfoods_link": f"https://www.youtube.com/watch?v={v['id']}",
            "kunfoods_id": v['id'],
            "foodfusion_video": None, "foodfusion_link": None, "foodfusion_id": None,
            "description": "", "ingredients": [], "ingredient_keys": [],
            "is_dessert": classify_dessert(v['title']), "is_salad": classify_salad(v['title']),
        }
    for v in new_foodfusion:
        key = normalize_title_key(v['title'])
        if key in new_recipes_map:
            entry = new_recipes_map[key]
            entry['foodfusion_video'] = v['title']
            entry['foodfusion_link'] = f"https://www.youtube.com/watch?v={v['id']}"
            entry['foodfusion_id'] = v['id']
            entry['channels'] = "2 channels"
        elif key in existing_titles:
            # matches an existing KunFoods-only entry — attach FoodfusionPk side to it
            entry = existing_titles[key]
            entry['foodfusion_video'] = v['title']
            entry['foodfusion_link'] = f"https://www.youtube.com/watch?v={v['id']}"
            entry['foodfusion_id'] = v['id']
            entry['channels'] = "2 channels"
            if not entry.get('ingredients') and not entry.get('sub_recipes'):
                # the existing side had no ingredients — this new video might have them
                enriched_existing.append((entry, v['id']))
        else:
            new_recipes_map[key] = {
                "dish": v['title'], "cuisine": classify_cuisine(v['title']), "channels": "1 channel",
                "kunfoods_video": None, "kunfoods_link": None, "kunfoods_id": None,
                "foodfusion_video": v['title'], "foodfusion_link": f"https://www.youtube.com/watch?v={v['id']}",
                "foodfusion_id": v['id'],
                "description": "", "ingredients": [], "ingredient_keys": [],
                "is_dessert": classify_dessert(v['title']), "is_salad": classify_salad(v['title']),
            }

    new_recipes = list(new_recipes_map.values())
    print(f"      -> {len(new_recipes)} new recipe entries after cross-channel matching"
          f" ({len(enriched_existing)} existing entries also gained a new video link)")

    # Anything needing a fresh description fetch: brand-new entries (using whichever
    # video id they have), plus existing entries that just gained a video link on the
    # side that had no ingredients yet (using specifically that new id, not the old one).
    to_process = [(r, r['kunfoods_id'] or r['foodfusion_id']) for r in new_recipes] + enriched_existing

    # Stage 3+4: fetch & parse YouTube descriptions
    use_cookies = setup_youtube_cookies()
    video_ids_to_fetch = [vid for _, vid in to_process]
    descriptions = fetch_descriptions(video_ids_to_fetch, use_cookies)

    print("[5/7] Parsing ingredients from descriptions...")
    for r, vid in to_process:
        desc = descriptions.get(vid, "")
        r['description'] = desc
        if desc:
            raw_names = parse_ingredients_from_description(desc)
            paired, keys = clean_ingredients(raw_names)
            r['ingredients'] = paired
            r['ingredient_keys'] = list(keys)

    # Stage 5: scrape foodfusion.com written recipes for anything with a bit.ly link
    single_targets = {}   # dish -> url
    multi_targets = {}    # dish -> [(label, url), ...]
    for r, _ in to_process:
        if r['ingredients']:
            continue  # already has good ingredients from the description itself
        if not r['description']:
            continue
        single_url, labeled = extract_written_recipe_links(r['description'])
        if single_url:
            single_targets[r['dish']] = single_url
        elif labeled:
            multi_targets[r['dish']] = labeled

    all_urls = set(single_targets.values())
    for links in multi_targets.values():
        all_urls.update(url for _, url in links)

    if all_urls:
        scraped = scrape_written_recipes(list(all_urls))
        for r, _ in to_process:
            dish = r['dish']
            if dish in single_targets:
                data = scraped.get(single_targets[dish])
                if data and data.get('ingredients'):
                    paired, keys = clean_ingredients([i['name'] for i in data['ingredients']])
                    if paired:
                        r['ingredients'] = paired
                        r['ingredient_keys'] = list(keys)
                        r['directions'] = data.get('directions', '')
                        r['source_url'] = single_targets[dish]
            elif dish in multi_targets:
                sub_recipes = []
                for label, url in multi_targets[dish]:
                    data = scraped.get(url)
                    if data and data.get('ingredients'):
                        paired, _ = clean_ingredients([i['name'] for i in data['ingredients']])
                        if paired:
                            sub_recipes.append({
                                "label": label, "ingredients": paired,
                                "directions": data.get('directions', ''), "source_url": url
                            })
                if sub_recipes:
                    r['sub_recipes'] = sub_recipes
    else:
        print("[6/7] No written-recipe links to scrape for this batch.")

    # Stage 7: merge & save
    print("[7/7] Merging into index.html and Merged_Recipes.csv...")
    final_recipes = existing_recipes + new_recipes
    write_recipes_to_html(html, final_recipes)
    write_merged_csv(final_recipes)

    covered = sum(1 for r in final_recipes if r.get('ingredients') or r.get('sub_recipes'))
    print("\n" + "=" * 60)
    print(f"Done. {len(new_recipes)} new recipes added.")
    print(f"Total: {len(final_recipes)} recipes, {covered} with ingredients ({covered*100//len(final_recipes)}%).")
    print("index.html and Merged_Recipes.csv have been updated in place.")
    print("Review the changes, then commit & push when you're happy with them:")
    print("  git add -A && git commit -m 'Update recipes' && git push")
    print("=" * 60)


if __name__ == '__main__':
    main()
