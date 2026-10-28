"""Preview images of the G-code stencil quine. Needs Pillow.

    python3 render.py

Runs stencil.ngc in the simulator and draws every cut, at its exact size, as a hole in a sheet:
stencil.png shows the whole sheet, and closeup.png its top-left corner, where the text begins.
"""

import os

from PIL import Image, ImageDraw

from gen_stencil import COLUMN, ROWS, PITCH
from ngcsim import run

HERE = os.path.dirname(os.path.abspath(__file__))
SHEET, HOLE = (226, 200, 150), (40, 34, 30)        # plywood, and the light behind it
MARGIN = 6                                         # mm around the text


def draw(cuts, scale, box):
    """Draw the cuts at `scale` pixels per mm inside `box` = (x0, y0, x1, y1) in mm, y down."""
    x0, y0, x1, y1 = box
    im = Image.new('RGB', (round((x1 - x0) * scale), round((y1 - y0) * scale)), SHEET)
    d = ImageDraw.Draw(im)
    for path in cuts:
        xs, ys = [p[0] for p in path], [-p[1] for p in path]
        if max(xs) < x0 or min(xs) > x1 or max(ys) < y0 or min(ys) > y1:
            continue
        d.rectangle([(min(xs) - x0) * scale, (min(ys) - y0) * scale,
                     (max(xs) - x0) * scale - 1, (max(ys) - y0) * scale - 1], fill=HOLE)
    return im


with open(os.path.join(HERE, 'stencil.ngc'), encoding='ascii') as f:
    source = f.read()
cuts = run(source)
columns = (source.count('\n') + ROWS) // ROWS
width, height = columns * COLUMN, ROWS * 9 * PITCH
draw(cuts, 4, (-MARGIN, -MARGIN, width - COLUMN + 32 * 6 * PITCH + MARGIN, height + MARGIN)) \
    .save(os.path.join(HERE, 'stencil.png'), optimize=True)
draw(cuts, 25, (-2, -2, 58, 32)).save(os.path.join(HERE, 'closeup.png'), optimize=True)
print(f'wrote stencil.png and closeup.png ({columns} columns, {width:g} x {height:g} mm)')
