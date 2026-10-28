#!/usr/bin/env python3
"""Independent check of the self-plotting formula (Python standard library only).

    python3 check.py            check formula.txt and plot.pbm, then write plot.png

The formula `0<E,k=` / `<digits>` denotes the points (x, y) of N^2 with 0 < E(x, y, k), where
`-` truncates at 0 and `/` rounds down. The checks:

1. this script's own parser and evaluator plot the formula, and the result equals plot.pbm,
   which Lean computed;
2. the plot equals the typesetting of formula.txt with font.txt (glyphs right-aligned at column
   W, line 0 at the bottom, y pointing up);
3. reading the plot back with the font gives formula.txt, character for character;
4. the formula is false at sampled points far outside the text.
"""

import random
import re
import struct
import sys
import zlib
from pathlib import Path

HERE = Path(__file__).resolve().parent


def read_font(path):
    font = {}
    for line in path.read_text().splitlines():
        if line:
            char, *rows = line.split(' ')
            font[char] = rows
    return font


def glyph_pixels(rows):
    """The set of (col, row-from-bottom) pixels of a glyph in its 4x6 cell."""
    return {(c, 4 - i) for i, row in enumerate(rows) for c, ch in enumerate(row) if ch == '#'}


def evaluate(expr, x, y, k):
    toks = re.findall(r'\d+|[xyk]|[-+*/%^()]', expr)
    if ''.join(toks) != expr:
        raise ValueError('unexpected character in formula')
    pos = 0

    def peek():
        return toks[pos] if pos < len(toks) else None

    def take():
        nonlocal pos
        pos += 1
        return toks[pos - 1]

    def atom():
        t = take()
        if t == '(':
            v = total()
            if take() != ')':
                raise ValueError('expected )')
            return v
        return {'x': x, 'y': y, 'k': k}[t] if t in 'xyk' else int(t)

    def power():
        base = atom()
        return base ** atom() if peek() == '^' and take() else base

    def product():
        v = power()
        while peek() in ('*', '/', '%'):
            op, w = take(), None
            w = power()
            v = v * w if op == '*' else (v // w if w else 0) if op == '/' else (v % w if w else v)
        return v

    def total():
        v = product()
        while peek() in ('+', '-'):
            op = take()
            w = product()
            v = v + w if op == '+' else max(v - w, 0)
        return v

    value = total()
    if pos != len(toks):
        raise ValueError('trailing input')
    return value


def parse(formula):
    top, bottom = formula.split('\n')
    if not (top.startswith('0<') and top.endswith(',k=') and bottom.isdigit()):
        raise ValueError('formula does not have the form 0<E,k= / digits')
    return top[2:-3], int(bottom)


def typeset(lines, font, width):
    """Pixels of the two lines (top first), right-aligned at column `width`, y pointing up."""
    pixels = set()
    for line_index, line in enumerate(reversed(lines)):          # line 0 is the bottom line
        for p, char in enumerate(reversed(line)):                 # cell p counted from the right
            for c, r in glyph_pixels(font[char]):
                pixels.add((4 * (width - 1 - p) + c, 6 * line_index + r))
    return pixels


def read_plot(pixels, font, width):
    """Read the text back: decode every cell, left to right, skipping blank cells."""
    by_glyph = {frozenset(glyph_pixels(rows)): char for char, rows in font.items()}
    lines = []
    for line_index in (1, 0):
        text = ''
        for col in range(width):
            cell = frozenset((x - 4 * col, y - 6 * line_index) for x, y in pixels
                             if x // 4 == col and y // 6 == line_index)
            if cell:
                text += by_glyph.get(cell, '?')
        lines.append(text)
    return '\n'.join(lines)


def read_pbm(path):
    tokens = path.read_text().split()
    assert tokens[0] == 'P1'
    w, h = int(tokens[1]), int(tokens[2])
    bits = ''.join(tokens[3:])
    return {(x, h - 1 - row) for row in range(h) for x in range(w) if bits[row * w + x] == '1'}, w, h


def write_png(path, pixels, w, h, scale=3, margin=2):
    W, H = (w + 2 * margin) * scale, (h + 2 * margin) * scale
    raw = bytearray()
    for Y in range(H):
        raw.append(0)
        y = h - 1 - (Y // scale - margin)
        for X in range(W):
            x = X // scale - margin
            raw.append(0 if (x, y) in pixels else 255)

    def chunk(kind, data):
        return struct.pack('>I', len(data)) + kind + data + struct.pack('>I', zlib.crc32(kind + data))

    png = b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', struct.pack('>IIBBBBB', W, H, 8, 0, 0, 0, 0))
    png += chunk(b'IDAT', zlib.compress(bytes(raw), 9)) + chunk(b'IEND', b'')
    path.write_bytes(png)


def main():
    font = read_font(HERE / 'font.txt')
    formula = (HERE / 'formula.txt').read_text()
    expr, k = parse(formula)
    lines = formula.split('\n')
    width = max(len(line) for line in lines)
    lean_plot, w, h = read_pbm(HERE / 'plot.pbm')

    plot = {(x, y) for y in range(h) for x in range(w) if evaluate(expr, x, y, k) > 0}
    assert plot == lean_plot, 'the plot computed here differs from the plot computed by Lean'
    print(f'1. evaluated {w}x{h} points: the plot equals plot.pbm ({len(plot)} black pixels)')

    assert plot == typeset(lines, font, width), 'the plot differs from the typeset formula'
    print(f'2. the plot equals the typesetting of formula.txt (width {width} cells)')

    assert read_plot(plot, font, width) == formula, 'reading the plot back does not give formula.txt'
    print(f'3. reading the plot back gives formula.txt ({len(formula)} characters)')

    rng = random.Random(0)
    far = [(rng.randrange(w, 10 ** 6), rng.randrange(0, 10 ** 4)) for _ in range(200)]
    far += [(rng.randrange(0, w), rng.randrange(h, 10 ** 4)) for _ in range(200)]
    assert all(evaluate(expr, x, y, k) == 0 for x, y in far)
    print('4. the formula is false at 400 sampled points outside the text')

    write_png(HERE / 'plot.png', plot, w, h)
    print('wrote plot.png')


if __name__ == '__main__':
    sys.exit(main())
