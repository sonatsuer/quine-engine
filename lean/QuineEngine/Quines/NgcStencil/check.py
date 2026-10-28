"""Empirical checks for the G-code stencil quine.

    python3 check.py [file.ngc]

The default file is stencil.ngc in this folder, written by `lake exe quine`, together with
stencil.pbm, the stencil that Lean predicts (one pixel per 0.6 mm). `ngcsim.py` runs a file and
returns the closed loops it cuts with the laser on; this script reads them back as text.

Reading the stencil: the bars of a cell form a 5 x 7 glyph of the SvgText font, read with that
font; cells without bars are spaces. Lines run in rows of 80 to a column, columns left to right,
and a line holds at most 32 characters.
"""

import os
import random
import sys

from gen_stencil import ALPHABET, COLUMN, PITCH, ROWS
from ngcsim import run

HERE = os.path.dirname(os.path.abspath(__file__))
CELL_W, CELL_H = 6 * PITCH, 9 * PITCH
with open(os.path.join(HERE, 'stencil.ngc.inc'), encoding='ascii') as f:
    LIB = f.read()

FONT = {}
with open(os.path.join(HERE, '..', 'SvgText', 'font5x7.txt')) as f:
    for line in f.read().splitlines():
        code, *rows = line.split(' ')
        FONT[sum(1 << (5 * r + c) for r, row in enumerate(rows) for c, ch in enumerate(row)
                 if ch == '#')] = chr(int(code, 16))


def data_block(x):
    """Lean's `dataBlock`: 7 two-digit codes to a parameter from #1001, then a zero."""
    codes = [ALPHABET.index(c) + 1 for c in x]
    out, i = '', 1001
    for k in range(0, len(codes), 7):
        group = codes[k:k + 7] + [0] * (7 - len(codes[k:k + 7]))
        out += f'#{i}=' + ''.join(f'{c:02d}' for c in group) + '\n'
        i += 1
    return out + f'#{i}=' + '0' * 14 + '\n'


def quoted(t):
    """Lean's `quoteWith`: a file that stores `t` and cuts it (mode 0)."""
    return data_block(t) + LIB + 'O100CALL[0]\nM2'


def near(v, k):
    if abs(v - round(v)) > 1e-6:
        raise SystemExit(f'cut off the grid ({k} = {v})')
    return round(v)


def glyphs(cuts):
    """The glyph bits of each cell (line, column), after checking that the cuts form a stencil."""
    cells = {}                                   # (line, column) -> glyph bits
    bars = {}                                    # (line, column, row) -> [(a, b)]
    for path in cuts:
        xs, ys = {p[0] for p in path}, {p[1] for p in path}
        if len(path) != 5 or path[0] != path[-1] or len(xs) != 2 or len(ys) != 2:
            raise SystemExit(f'a cut is not a closed rectangle: {path}')
        x0, x1, y0 = min(xs), max(xs), max(ys)
        if abs(max(ys) - min(ys) - 0.36) > 1e-9:
            raise SystemExit(f'a bar of the wrong height: {path}')
        page = int(x0 // COLUMN)
        u, v = x0 - page * COLUMN, -y0
        col, line = int(u // CELL_W), int(v // CELL_H)
        a = near((u - col * CELL_W - 0.06) / PITCH, 'start')
        b = near((x1 - page * COLUMN - col * CELL_W - 0.54) / PITCH, 'end')
        r = near((v - line * CELL_H - 0.12) / PITCH, 'row')
        if not (0 <= a <= b < 5 and 0 <= r < 7 and line < ROWS):
            raise SystemExit(f'a bar outside its glyph: {path}')
        key = (page * ROWS + line, col)
        for c in range(a, b + 1):
            bit = 1 << (5 * r + c)
            if cells.get(key, 0) & bit:
                raise SystemExit(f'overlapping bars at {key}')
            cells[key] = cells.get(key, 0) | bit
        bars.setdefault(key + (r,), []).append((a, b))
    # The stencil property: bars of one row are separated by at least one empty pixel, so every
    # bar is surrounded by uncut material and the strips between rows run unbroken.
    for runs in bars.values():
        runs.sort()
        for (_, b), (a, _) in zip(runs, runs[1:]):
            if a <= b + 1:
                raise SystemExit('two bars of one row touch')
    return cells


def bitmap(cells):
    """The cut pixels, one per 0.6 mm, as in Lean's `stencil`: 200 pixels to a column."""
    return {((line // ROWS) * 200 + col * 6 + k % 5, (line % ROWS) * 9 + k // 5)
            for (line, col), g in cells.items() for k in range(35) if g >> k & 1}


def read(cuts):
    """Read the cut loops back as text."""
    cells = glyphs(cuts)
    lines = {}
    for (line, col), g in cells.items():
        if g not in FONT:
            raise SystemExit(f'an unknown glyph at line {line}, column {col}')
        lines.setdefault(line, {})[col] = FONT[g]
    n = max(lines) + 1 if lines else 0
    def text(row):
        return ''.join(row.get(c, ' ') for c in range(max(row) + 1))
    return '\n'.join(text(lines[l]) if l in lines else '' for l in range(n))


def check_library():
    rng = random.Random(1)
    printable = ALPHABET.replace('\n', '')
    tests = [printable[:32] + '\n' + printable[32:], printable[::-1][:20] + '\n\n\nX', 'X']
    for _ in range(6):
        lines = [''.join(rng.choice(printable) for _ in range(rng.randrange(1, 33)))
                 for _ in range(rng.randrange(1, 90))]
        tests.append('\n'.join(lines))
    for t in tests:
        if read(run(quoted(t))) != t:
            raise SystemExit(f'library: the stencil of a {len(t)}-character text does not read '
                             'back')
    print(f'library: {len(tests)} texts, including the whole alphabet and over 80 lines, read back')


def check_quine(path):
    with open(path, encoding='ascii') as f:
        source = f.read()
    cuts = run(source)
    predicted = os.path.join(os.path.dirname(path), 'stencil.pbm')
    if os.path.exists(predicted):
        with open(predicted, encoding='ascii') as f:
            _, size, *rows = f.read().split('\n')
        lean = {(x, y) for y, row in enumerate(rows) for x, ch in enumerate(row) if ch == '1'}
        if bitmap(glyphs(cuts)) != lean:
            raise SystemExit(f'{path}: the cut pixels differ from stencil.pbm (Lean)')
        print(f'{path}: the cut pixels are stencil.pbm ({size}), as Lean predicts')
    reading = read(cuts)
    if reading != source:
        raise SystemExit(f'{path}: the stencil does not read back to the source')
    print(f'{path}: {len(source)} characters on {source.count(chr(10)) + 1} lines, cut as '
          f'{len(cuts)} bars; the stencil reads back to the source')


if __name__ == '__main__':
    check_library()
    check_quine(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'stencil.ngc'))
