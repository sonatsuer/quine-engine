"""Empirical checks for the Python braille quine. Needs Python 3 only.

    python3 check.py [file.py]

The default file is braille.py in this folder, written by `lake exe quine`, together with
braille.txt, the braille that Lean's `render` predicts. The reference NABCC table is copied from
liblouis (see `NABCC`).
"""

import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PRINTABLE = ''.join(chr(n) for n in range(32, 127))
# NABCC, as Unicode braille, for the printable characters 32-126 in order. Copied from the table
# en-nabcc.utb of liblouis 3.29.0 (https://github.com/liblouis/liblouis/blob/v3.29.0/tables/en-nabcc.utb),
# which translates each character on its own.
NABCC = '⠀⠮⠐⠼⠫⠩⠯⠄⠷⠾⠡⠬⠠⠤⠨⠌⠴⠂⠆⠒⠲⠢⠖⠶⠦⠔⠱⠰⠣⠿⠜⠹⡈⡁⡃⡉⡙⡑⡋⡛⡓⡊⡚⡅⡇⡍⡝⡕⡏⡟⡗⡎⡞⡥⡧⡺⡭⡽⡵⡪⡳⡻⡘⠸⠈⠁⠃⠉⠙⠑⠋⠛⠓⠊⠚⠅⠇⠍⠝⠕⠏⠟⠗⠎⠞⠥⠧⠺⠭⠽⠵⠪⠳⠻⠘'


def nabcc(text):
    """The NABCC of a text, as Unicode braille (newlines stay newlines)."""
    return ''.join(c if c == '\n' else NABCC[ord(c) - 32] for c in text)


def run(path):
    return subprocess.run([sys.executable, path], check=True, capture_output=True).stdout


def check_library():
    # The library alone, made to show the printable characters.
    with open(os.path.join(HERE, 'braille.py.inc'), encoding='ascii') as f:
        lib = f.read()
    env = {}
    exec(lib, env)
    got = ''.join(map(env['cell'], PRINTABLE + '\n'))
    if got != nabcc(PRINTABLE + '\n'):
        raise SystemExit('library: cell differs from the NABCC table')
    if len(set(got)) != len(got):
        raise SystemExit('library: two characters share a cell')
    print(f'library: cell agrees with the NABCC table on all {len(PRINTABLE)} printable '
          'characters and newline, and is one-to-one')


def check_quine(path):
    with open(path, encoding='ascii') as f:
        source = f.read()
    out = run(path).decode('utf-8')
    predicted = os.path.join(os.path.dirname(path), 'braille.txt')
    if os.path.exists(predicted):
        with open(predicted, encoding='utf-8') as f:
            if out != f.read():
                raise SystemExit(f'{path}: the output differs from braille.txt (Lean)')
        print(f'{path}: the output is braille.txt, as Lean predicts')
    if out != nabcc(source):
        raise SystemExit(f'{path}: the output is not the NABCC of the source')
    # Read the output back, cell by cell, with the table.
    back = {nabcc(c): c for c in PRINTABLE + '\n'}
    if ''.join(back[b] for b in out) != source:
        raise SystemExit(f'{path}: the output does not read back to the source')
    print(f'{path}: {len(source)} characters; the output is its NABCC and reads back to it')


check_library()
check_quine(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'braille.py'))
