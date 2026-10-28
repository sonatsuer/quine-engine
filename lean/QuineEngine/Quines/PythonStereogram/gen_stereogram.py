#!/usr/bin/env python3
r"""Write the 16-segment table and the library of the stereogram quine.

    python3 gen_stereogram.py

The table is the single source of the characters and their segments:
- `font16.txt`, read by `PythonStereogram.lean`: one line per character, its code and its 16
  segments as 4 hex digits;
- `stereogram.py.inc`, the library: `stereogram.py.in` with the table filled in.

Segment i is bit i of: a1 a2 b c d1 d2 e f g1 g2 i l ul ur ll lr. These are the top halves, the
right side (upper, lower), the bottom halves, the left side (lower, upper), the middle halves, the
centre bar (upper, lower), and the diagonals from the corners to the centre.

The library sits in a Python triple-quoted literal and is shown on the pages, so it must have no
double quote, no backslash, no capital letters, and only characters of the table.
"""

from pathlib import Path

HERE = Path(__file__).resolve().parent
NAMES = 'a1 a2 b c d1 d2 e f g1 g2 i l ul ur ll lr'.split()
FONT = {
    'a': 'a1 a2 b c e f g1 g2', 'b': 'f e d1 d2 c g1 g2', 'c': 'a1 a2 f e d1 d2',
    'd': 'a1 a2 b c d1 d2 i l', 'e': 'a1 a2 f e d1 d2 g1', 'f': 'a1 a2 f e g1',
    'g': 'a1 a2 f e d1 d2 c g2', 'h': 'f e b c g1 g2', 'i': 'a1 a2 i l d1 d2', 'j': 'b c d1 d2 e',
    'k': 'f e g1 ur lr', 'l': 'f e d1 d2', 'm': 'f e b c ul ur', 'n': 'f e b c ul lr',
    'o': 'a1 a2 b c d1 d2 e f', 'p': 'a1 a2 b f e g1 g2', 'q': 'a1 a2 b c d1 d2 e f lr',
    'r': 'a1 a2 b f e g1 g2 lr', 's': 'a1 a2 ul g2 c d1 d2', 't': 'a1 a2 i l',
    'u': 'f e d1 d2 c b', 'v': 'e c d1 d2', 'w': 'f e b c ll lr', 'x': 'ul ur ll lr',
    'y': 'ul ur l', 'z': 'a1 a2 ur ll d1 d2',
    '0': 'a1 a2 b c d1 d2 e f ur ll', '1': 'b c ur', '2': 'a1 a2 b g1 g2 e d1 d2',
    '3': 'a1 a2 b c d1 d2 g2', '4': 'f g1 g2 b c', '5': 'a1 a2 f g1 g2 c d1 d2',
    '6': 'a1 a2 f e d1 d2 c g1 g2', '7': 'a1 a2 b c', '8': 'a1 a2 b c d1 d2 e f g1 g2',
    '9': 'a1 a2 b c d1 d2 f g1 g2',
    ' ': '', '\n': ' '.join(NAMES),
    '(': 'ur lr', ')': 'ul ll', '[': 'a1 f e d1', ']': 'a2 b c d2', '{': 'a2 i l d2 g1',
    '}': 'a1 i l d1 g2', '<': 'ur lr g1', '>': 'ul ll g2', '=': 'g1 g2 d1 d2', '+': 'g1 g2 i l',
    '-': 'g1 g2', '*': 'ul ur ll lr g1 g2 i l', '/': 'ur ll', '%': 'ur ll f a1 c d2',
    '&': 'a1 i g1 e d1 lr ul', '|': 'i l', '^': 'll lr', '.': 'd2', ',': 'll', ':': 'g2 d2',
    ';': 'g2 ll', "'": 'i', '"': 'f i', '#': 'i l b c g1 g2', '_': 'd1 d2', '!': 'b d2',
    '?': 'a1 a2 b g2 l', '@': 'a1 a2 b c d1 d2 e f g2 i', '~': 'e g1 g2 b',
}
ALL = {ch: sum(1 << NAMES.index(n) for n in segs.split()) for ch, segs in FONT.items()}
if len(set(ALL.values())) != len(ALL):
    raise SystemExit('two characters share a pattern')
# the alphabet: every letter and digit, the space and the line break, and the punctuation that the
# program uses (including the template's `"`). Each key costs 5 bytes of the program, so unused
# punctuation is left out.
TEMPLATE = ('v=\"\"\";exec(v)'
            "draw('v='+chr(34)+chr(34)+chr(34)+v+chr(34)+chr(34)+chr(34)+';exec(v)'+chr(10))")
src = (HERE / 'stereogram.py.in').read_text().replace('@KEYS@', '').replace('@CODES@', '')
need = set(src + TEMPLATE) | set('abcdefghijklmnopqrstuvwxyz0123456789 \n')
CODES = {ch: code for ch, code in ALL.items() if ch in need}
KEYS = ''.join(CODES)

(HERE / 'font16.txt').write_text(''.join(f'{ord(ch):02x} {CODES[ch]:04x}\n' for ch in KEYS))

# the keys as a Python expression without a double quote or backslash: the quote characters and
# the line break are written with chr
parts, cur = [], ''
for ch in KEYS:
    if ch in '\'"\n':
        if cur:
            parts.append("'" + cur + "'")
        parts.append(f'chr({ord(ch)})')
        cur = ''
    else:
        cur += ch
if cur:
    parts.append("'" + cur + "'")
lib = (HERE / 'stereogram.py.in').read_text()
lib = lib.replace('@KEYS@', ' + '.join(parts)).replace('@CODES@', ''.join(
    f'{CODES[ch]:04x}' for ch in KEYS))
bad = sorted(set(ch for ch in lib if ch not in CODES or ch in '"\\' or ch.isupper()))
if bad:
    raise SystemExit(f'the library uses characters it cannot show: {bad}')
(HERE / 'stereogram.py.inc').write_text(lib)
print(f'wrote font16.txt ({len(KEYS)} characters) and stereogram.py.inc ({len(lib)} bytes)')
