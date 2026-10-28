#!/usr/bin/env python3
"""Generate encoder.gp.inc from encoder-source.gp.

    python3 gen_encoder.py

The quine's code must be a single line without `'`, so that it can sit in a gnuplot `'…'` literal.
The source has one statement or block per line; this joins the lines with `;`.
"""

from pathlib import Path

HERE = Path(__file__).resolve().parent
lines = [l.strip() for l in (HERE / 'encoder-source.gp').read_text().splitlines() if l.strip()]
enc = ';'.join(lines)
assert "'" not in enc, 'the library must not contain a single quote'
assert all(32 <= ord(c) < 127 for c in enc), 'the library must be printable ASCII'
(HERE / 'encoder.gp.inc').write_text(enc)
print(f'wrote encoder.gp.inc ({len(enc)} bytes)')
