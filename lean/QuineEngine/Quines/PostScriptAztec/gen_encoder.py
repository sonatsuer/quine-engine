#!/usr/bin/env python3
"""Generate encoder.ps.inc from encoder-source.ps.inc.

    python3 gen_encoder.py

The readable Aztec encoder (encoder-source.ps.inc, about 3.2 KB) does not fit inside the Aztec code
it draws, whose capacity is 2,278 bytes. So encoder.ps.inc is a short loader instead: it holds the
source, joined onto one line, compressed with zlib and written in Base64; at run time it decodes the
Base64, decompresses it with PostScript's FlateDecode filter, and executes the result, which defines
`cat` and `Q`. The loader must not contain a backslash or `%`, and its parentheses must balance, so
that it can sit unescaped inside a PostScript string literal. Base64 without `=` padding satisfies
this.
"""

import base64
import re
import zlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALPHABET = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'

source = re.sub(r'\s+', ' ', (HERE / 'encoder-source.ps.inc').read_text()).strip()
packed = zlib.compress(source.encode(), 9)
packed += b'\0' * (-len(packed) % 3)          # no '=' padding: FlateDecode stops at the stream's end
data = base64.b64encode(packed).decode()
loader = (
    f"/K ({ALPHABET}) def /T 256 string def 0 1 63{{/i exch def T K i get i put}}for "
    f"/D ({data}) def /O D length 4 idiv 3 mul string def "
    "0 1 D length 4 idiv 1 sub{/i exch def /v 0 def 0 1 3{i 4 mul add D exch get T exch get "
    "v 6 bitshift add /v exch def}for O i 3 mul v -16 bitshift put O i 3 mul 1 add v -8 bitshift "
    "255 and put O i 3 mul 2 add v 255 and put}for O /FlateDecode filter cvx exec"
)
assert '\\' not in loader and '%' not in loader and '\n' not in loader
depth = 0
for ch in loader:
    depth += {'(': 1, ')': -1}.get(ch, 0)
    assert depth >= 0
assert depth == 0
(HERE / 'encoder.ps.inc').write_text(loader)
print(f'wrote encoder.ps.inc ({len(loader)} bytes, from {len(source)} bytes of source)')
