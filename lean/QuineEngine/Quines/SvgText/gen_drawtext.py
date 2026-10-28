#!/usr/bin/env python3
"""Generate drawtext.js.inc from font5x7.txt.

    python3 gen_drawtext.py

The renderer draws a text in the 5x7 font, 80 characters per row, each glyph in a 6x8 cell. The
font is embedded as a Base64 string: bit 35*g + 5*r + c (most significant bit first in each byte)
is pixel (c, r) of the glyph for character code 32 + g, with r counted from the top. The output
must not contain `"`, `\\`, `<` or `&`, so that it can sit unescaped in an SVG script literal.
"""

import base64
from pathlib import Path

HERE = Path(__file__).resolve().parent
W = 80

glyphs = {}
for line in (HERE / 'font5x7.txt').read_text().splitlines():
    code, *rows = line.split(' ')
    glyphs[int(code, 16)] = rows

bits = []
for code in range(32, 127):
    for row in glyphs[code]:
        bits += [1 if ch == '#' else 0 for ch in row]
bits += [0] * (-len(bits) % 8)
data = bytes(int(''.join(map(str, bits[i:i + 8])), 2) for i in range(0, len(bits), 8))
font = base64.b64encode(data).decode()

js = (
    "H=String.fromCharCode;drawText=s=>{F=atob('" + font + "');P='';"
    "for(i=0;s.length>i;i++)for(g=s.charCodeAt(i)-32,r=0;7>r;r++)for(c=0;5>c;c++)"
    "if((F.charCodeAt((b=35*g+5*r+c)>>3)>>7-b%8)%2)P+=`M${i%" + str(W) + "*6+c},${(i/" + str(W)
    + "|0)*8+r}h1v1h-1`;"
    "x=document.documentElement;y=document.createElementNS(x.namespaceURI,'path');"
    "x.setAttribute('viewBox',`0 0 " + str(6 * W) + " ${8*Math.ceil(s.length/" + str(W) + ")}`);"
    "x.style.background='#fff';y.setAttribute('d',P);x.append(y)}"
)
for bad in '"\\<&':
    assert bad not in js, bad
assert ']]>' not in js
(HERE / 'drawtext.js.inc').write_text(js)
print(f'wrote drawtext.js.inc ({len(js)} bytes)')
