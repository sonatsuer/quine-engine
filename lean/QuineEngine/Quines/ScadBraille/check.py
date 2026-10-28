"""Empirical checks for the OpenSCAD braille quine. Needs OpenSCAD.

    python3 check.py [file.scad]

The default file is braille.scad in this folder, written by `lake exe quine`, together with
braille.txt, the reading that Lean's `render` predicts. OpenSCAD evaluates a file to its CSG tree,
which lists every plate and every dot; the dots are read back as braille. The reference is the
NABCC table copied from liblouis (see `NABCC`), without dots 7 and 8, which is Braille ASCII.

Reading the plates: rows run left to right, top to bottom, plate after plate. A row followed
directly by another is full (32 cells; cells without dots are spaces), and each blank row is a
line break.
"""

import os
import random
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
W, H = 32, 20                      # cells a row, rows a plate
PAGE = W * 6 + 14                  # plate pitch
ALPHABET = ''.join(chr(n) for n in list(range(32, 65)) + list(range(91, 96)) + list(range(97, 123)))
with open(os.path.join(HERE, 'braille.scad.inc'), encoding='ascii') as f:
    ENC = f.read()
# NABCC, as Unicode braille, for the printable characters 32-126 in order. Copied from the table
# en-nabcc.utb of liblouis 3.29.0 (https://github.com/liblouis/liblouis/blob/v3.29.0/tables/en-nabcc.utb),
# which translates each character on its own.
NABCC = '⠀⠮⠐⠼⠫⠩⠯⠄⠷⠾⠡⠬⠠⠤⠨⠌⠴⠂⠆⠒⠲⠢⠖⠶⠦⠔⠱⠰⠣⠿⠜⠹⡈⡁⡃⡉⡙⡑⡋⡛⡓⡊⡚⡅⡇⡍⡝⡕⡏⡟⡗⡎⡞⡥⡧⡺⡭⡽⡵⡪⡳⡻⡘⠸⠈⠁⠃⠉⠙⠑⠋⠛⠓⠊⠚⠅⠇⠍⠝⠕⠏⠟⠗⠎⠞⠥⠧⠺⠭⠽⠵⠪⠳⠻⠘'


def ascii_braille(text):
    """The Braille ASCII cells of a text: NABCC without dots 7 and 8 (newlines stay newlines)."""
    return ''.join(c if c == '\n' else chr(0x2800 + ((ord(NABCC[ord(c) - 32]) - 0x2800) & 63))
                   for c in text)


READ = {ascii_braille(c): c for c in ALPHABET}


def evaluate(path):
    """Plates and dots of a file, from OpenSCAD's CSG tree."""
    with tempfile.TemporaryDirectory() as work:
        csg = os.path.join(work, 'model.csg')
        subprocess.run(['openscad', '-o', csg, path], check=True, capture_output=True)
        with open(csg) as f:
            tree = f.read()
    num = r'(-?[\d.e+-]+)'
    at = rf'multmatrix\(\[\[1, 0, 0, {num}\], \[0, 1, 0, {num}\], \[0, 0, 1, {num}\], ' \
        r'\[0, 0, 0, 1\]\]\) \{\s*'
    plates = [tuple(map(float, m)) for m in re.findall(at + r'cube\(', tree)]
    dots = [tuple(map(float, m)) for m in re.findall(at + r'cylinder\(', tree)]
    if len(dots) != tree.count('cylinder(') or len(plates) != tree.count('cube('):
        raise SystemExit(f'{path}: unexpected shapes in the CSG tree')
    return plates, dots


def read(plates, dots):
    """Read the dots as rows of cells, then as text with line breaks."""
    cells = {}                    # (row, column) -> dots
    for x, y, _ in dots:
        page = int(x // PAGE)
        u, v = x - page * PAGE - 4, -y - 4
        col, row = round(u // 6), round(v // 10)
        dx, dy = round((u - 6 * col) / 2.5), round((v - 10 * row) / 2.5)
        k = 3 * dx + dy
        key = (page * H + row, col)
        cells[key] = cells.get(key, 0) | (1 << k)
    if len(plates) != (max(r for r, _ in cells) // H + 1 if cells else 1):
        raise SystemExit('the number of plates does not match the rows')
    rows = {}
    for (r, c), m in cells.items():
        rows.setdefault(r, {})[c] = m
    text, last = '', -1
    for r in sorted(rows):
        gap = r - last - 1
        if last >= 0 and gap == 0:
            text += chr(0x2800) * (W - len(line))     # the previous row was full
        text += '\n' * gap
        width = max(rows[r]) + 1
        line = ''.join(chr(0x2800 + rows[r].get(c, 0)) for c in range(width))
        text += line
        last = r
    return text


def quoted(t):
    """Lean's `quoteWith`: a file that binds `t`, escaped, to `s` and shows it."""
    return 's="' + ''.join(f'\\x{ord(c):02x}' for c in t) + '";\n' + ENC + 'braille(s);'


def check_library():
    tests = [ALPHABET, ALPHABET[:W] + '\n' + ALPHABET[W:], '\n\n' + ALPHABET + '\nab\n\ncd']
    rng = random.Random(1)
    for _ in range(5):
        lines = [''.join(rng.choice(ALPHABET) for _ in range(rng.randrange(0, 90))).rstrip()
                 for _ in range(rng.randrange(1, 12))]
        tests.append('\n'.join(lines).rstrip('\n') + 'x')
    ran = 0
    with tempfile.TemporaryDirectory() as work:
        path = os.path.join(work, 'test.scad')
        for t in tests:
            if any(set(row) == {' '} for row in re.findall(r'.{1,32}', t)):
                continue                              # a row of spaces only would be blank
            with open(path, 'w', encoding='ascii') as f:
                f.write(quoted(t))
            if read(*evaluate(path)) != ascii_braille(t):
                raise SystemExit(f'library: the plates for {t!r} do not read as its Braille ASCII')
            ran += 1
    print(f'library: {ran} texts, including all 64 characters, read back as their Braille '
          'ASCII')


def check_quine(path):
    with open(path, encoding='ascii') as f:
        source = f.read()
    plates, dots = evaluate(path)
    reading = read(plates, dots)
    predicted = os.path.join(os.path.dirname(path), 'braille.txt')
    if os.path.exists(predicted):
        with open(predicted, encoding='utf-8') as f:
            if reading != f.read():
                raise SystemExit(f'{path}: the plates differ from braille.txt (Lean)')
        print(f'{path}: the plates read as braille.txt, as Lean predicts')
    if reading != ascii_braille(source):
        raise SystemExit(f'{path}: the plates are not the Braille ASCII of the source')
    if ''.join(READ.get(b, b) for b in reading) != source:
        raise SystemExit(f'{path}: the plates do not read back to the source')
    print(f'{path}: {len(source)} characters on {len(plates)} plates with {len(dots)} dots; '
          'they read back to the source')


check_library()
check_quine(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'braille.scad'))
