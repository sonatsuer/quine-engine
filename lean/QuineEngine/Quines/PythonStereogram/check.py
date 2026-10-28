"""Empirical checks for the Python stereogram quine.

    python3 check.py [file.py]

The default file is stereogram.py in this folder, written by `lake exe quine`. With it comes
stereogram.txt, the segments that Lean's `render` predicts: one character a line, its 16 segments
as 4 hex digits.

Each program runs in a scratch folder and writes stereogram.pdf. The check parses the PDF and
verifies:
- **The title page** is first and says `I am a Quine`.
- **The links.** It rebuilds each page's depth map from the predicted segments, with its own copy
  of the layout. Then, for every dot of every page, it checks that the two dots half a separation
  to its left and right have the same colour: 140 px apart where the surface is flat, 112 px apart
  where it is raised. Flat points within 15 px of a raised one are left unlinked by design (the
  hidden-surface rule).
- **The reading.** From the dots alone, in each character's cell, it decides for each segment
  whether its area reads as raised (its 112 px pairs match more often than its 140 px pairs). The
  segments read this way must be the predicted ones, and decode to the source.
"""

import os
import random
import re
import subprocess
import sys
import tempfile
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
W, H, PW, PH = 1900, 1000, 1660, 900         # page and depth map, in pixels
SEP, DEP, LEFT, TOP = 140, 28, 120, 50       # separation, its change when raised, margins
with open(os.path.join(HERE, 'stereogram.py.inc'), encoding='ascii') as f:
    LIB = f.read()
CODE = {}
with open(os.path.join(HERE, 'font16.txt'), encoding='ascii') as f:
    for line in f.read().split('\n'):
        if line:
            a, b = line.split(' ')
            CODE[chr(int(a, 16))] = int(b, 16)
READ = {v: k for k, v in CODE.items()}


# ---- the layout, as the README describes it ----

def place(i):
    """The top-left corner of character i, on its page."""
    j = i % 24
    return 36 + j % 8 * 200 + i * 37 % 49, 28 + j // 8 * 300 + i * 23 % 25


def shape(n):
    """The pixels of segment n, as offsets from its character's corner: the character is
    140 x 220, with bars 26 px wide."""
    c, m = 70, 97
    bars = [(0, 0, c, 26), (c, 0, 140, 26), (114, 0, 140, m + 26), (114, m, 140, 220),
            (0, 194, c, 220), (c, 194, 140, 220), (0, m, 26, 220), (0, 0, 26, m + 26),
            (0, m, c, m + 26), (c, m, 140, m + 26),
            (c - 13, 0, c + 13, m + 26), (c - 13, m, c + 13, 220)]
    if n < 12:
        x0, y0, x1, y1 = bars[n]
        return {(u, v) for v in range(y0, y1) for u in range(x0, x1)}
    p, q = [(-44, -84), (44, -84), (-44, 84), (44, 84)][n - 12]    # corner, from the centre
    out = set()
    for w in range(-110, 110):
        for v in range(-70, 70):
            f = max(0, min(1, (v * p + w * q) / (p * p + q * q)))
            if (v - f * p) ** 2 + (w - f * q) ** 2 < 170:
                out.add((70 + v, 110 + w))
    return out


SHAPES = [shape(n) for n in range(16)]
# the part of each segment that no other segment covers, where its reading is taken
OWN = [sorted(SHAPES[n].difference(*(SHAPES[k] for k in range(16) if k != n))) for n in range(16)]
SHAPES = [sorted(s) for s in SHAPES]


def depth_map(codes, first):
    """The depth map of the page whose characters start at index `first`: 1 where raised."""
    z = bytearray(PW * PH)
    for i in range(first, min(first + 24, len(codes))):
        x, y = place(i)
        for n in range(16):
            if codes[i] >> n & 1:
                for u, v in SHAPES[n]:
                    z[(y + v) * PW + x + u] = 1
    return z


# ---- the PDF ----

def read_pdf(path):
    """The title page's text and each stereogram page's palette indices, in page order."""
    with open(path, 'rb') as f:
        data = f.read()
    if not data.startswith(b'%PDF-1.4'):
        raise SystemExit('not a PDF')
    obj = {}
    for m in re.finditer(rb'(\d+) 0 obj\n', data):
        n, start = int(m.group(1)), m.end()
        end = data.index(b'\nendobj\n', start)
        body = data[start:end]
        s = body.find(b'stream\n')
        obj[n] = (body[:s], body[s + 7:body.rindex(b'\nendstream')]) if s >= 0 else (body, None)
    kids = re.search(rb'/Kids\[([^]]*)\]', obj[2][0]).group(1)
    kids = [int(k) for k in re.findall(rb'(\d+) 0 R', kids)]
    title, images = None, []
    for k in kids:
        d = obj[k][0]
        content = obj[int(re.search(rb'/Contents (\d+) 0 R', d).group(1))][1]
        if b'/Font' in d:
            if images or title:
                raise SystemExit('the title page is not first')
            title = re.search(rb'\((.*)\)Tj', content).group(1).decode()
        else:
            im = obj[int(re.search(rb'/XObject<</i (\d+) 0 R', d).group(1))]
            if b'/Width 1900/Height 1000' not in im[0]:
                raise SystemExit('a page has the wrong size')
            images.append(im[1])
    pal = re.search(rb'/Indexed/DeviceRGB 255<([0-9a-f]+)>', obj[3][0]).group(1)
    pal = bytes.fromhex(pal.decode())
    if pal[:3] != bytes(3):
        raise SystemExit('palette entry 0 (the guide dots) is not black')
    return title, images


def in_dot(x, y):
    return min((x - 880) ** 2, (x - 1020) ** 2) + (y - 25) ** 2 <= 100


def check_links(img, z, page):
    """Every link of the page's depth map joins two dots of one colour."""
    for y in range(H):
        row = img[y * W:(y + 1) * W]
        if TOP <= y < TOP + PH:
            r = bytes(LEFT) + z[(y - TOP) * PW:(y - TOP + 1) * PW] + bytes(W - LEFT - PW)
        else:
            r = bytes(W)
        for x in range(W):
            s = SEP - DEP * r[x]
            a = x - s // 2
            b = a + s
            if a < 0 or b >= W or (not r[x] and 1 in r[max(0, x - 15):x + 16]):
                continue
            if row[a] != row[b] and not (in_dot(a, y) or in_dot(b, y)):
                raise SystemExit(f'page {page}: the dots around ({x}, {y}) are not linked')
    for g in (880, 1020):
        if img[25 * W + g] != 0:
            raise SystemExit(f'page {page}: a guide dot is missing')


def read_segments(img, codes, first):
    """Read the segments of the page's characters from the dots alone."""
    out = []
    for i in range(first, min(first + 24, len(codes))):
        x0, y0 = place(i)
        code = 0
        for n in range(16):
            near = flat = 0
            for u, v in OWN[n]:
                x, y = x0 + u + LEFT, y0 + v + TOP
                p = y * W
                a = img[p + x - 56] == img[p + x + 56]
                b = img[p + x - 70] == img[p + x + 70]
                near += a and not b
                flat += b and not a
            code |= (near > flat) << n
        out.append(code)
    return out


def check(source, codes, label, d):
    path = os.path.join(d, 'stereogram.py')
    with open(path, 'w', encoding='ascii') as f:
        f.write(source)
    r = subprocess.run([sys.executable, path], cwd=d, capture_output=True, text=True)
    if r.returncode or r.stdout:
        raise SystemExit(f'{label}: the program failed or printed:\n{r.stdout}{r.stderr}')
    title, images = read_pdf(os.path.join(d, 'stereogram.pdf'))
    if title != 'I am a Quine':
        raise SystemExit(f'{label}: the title page says {title!r}')
    if len(images) != (len(codes) + 23) // 24:
        raise SystemExit(f'{label}: {len(images)} pages, expected {(len(codes) + 23) // 24}')
    read = []
    for p, packed in enumerate(images):
        img = zlib.decompress(packed)
        if len(img) != W * H:
            raise SystemExit(f'{label}: page {p + 2} has the wrong length')
        check_links(img, depth_map(codes, 24 * p), p + 2)
        read += read_segments(img, codes, 24 * p)
    if read != codes:
        bad = [i for i, (a, b) in enumerate(zip(read, codes)) if a != b]
        raise SystemExit(f'{label}: {len(bad)} characters read wrongly, the first at {bad[0]}')
    return len(images)


def quoted(t):
    """Lean's `quoteWith`: a file that binds `t`, in hexadecimal, to `v` and draws it."""
    return ('v=bytes.fromhex("' + t.encode().hex() + '").decode();exec("""' + LIB
            + 'draw(v)""")\n')


def check_library():
    keys = ''.join(CODE)
    rng = random.Random(1)
    tests = [keys, keys[::-1], 'e']
    tests.append(''.join(rng.choice(keys) for _ in range(rng.randrange(25, 80))))
    with tempfile.TemporaryDirectory() as d:
        for t in tests:
            check(quoted(t), [CODE[c] for c in t], f'library {t[:12]!r}', d)
    print(f'library: {len(tests)} texts, including every one of the {len(keys)} characters, are '
          'drawn as linked autostereograms that read back to them')


def check_quine(path):
    with open(path, encoding='ascii') as f:
        source = f.read()
    codes = [CODE[c] for c in source]
    predicted = os.path.join(os.path.dirname(path), 'stereogram.txt')
    if os.path.exists(predicted):
        with open(predicted, encoding='ascii') as f:
            if [int(x, 16) for x in f.read().split()] != codes:
                raise SystemExit(f'{path}: the segments differ from stereogram.txt (Lean)')
        print(f'{path}: the segments are stereogram.txt, as Lean predicts')
    with tempfile.TemporaryDirectory() as d:
        n = check(source, codes, path, d)
    if ''.join(READ[c] for c in codes) != source:
        raise SystemExit(f'{path}: the segments do not decode to the source')
    print(f'{path}: {len(source)} bytes on a title page and {n} stereogram pages; every link '
          'holds, and the segments read from the dots decode to the source')


check_library()
check_quine(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'stereogram.py'))
