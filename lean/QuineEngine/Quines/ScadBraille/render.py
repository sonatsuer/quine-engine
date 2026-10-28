"""Preview images of the OpenSCAD braille quine. Needs OpenSCAD and Pillow.

    python3 render.py

Writes plates.png, all plates seen from above at a slight tilt, and closeup.png, the top-left
corner of the first plate, where the text begins. Both are OpenSCAD's own preview renderings of
braille.scad.
"""

import os
import subprocess
import tempfile

from PIL import Image, ImageChops

HERE = os.path.dirname(os.path.abspath(__file__))
SCAD = os.path.join(HERE, 'braille.scad')


def openscad(out, camera, projection, size):
    subprocess.run(['openscad', '-o', out, f'--camera={camera}', f'--projection={projection}',
                    f'--imgsize={size}', '--colorscheme=Tomorrow', SCAD],
                   check=True, capture_output=True)


def crop(path, margin=40):
    """Crop an image to its content and a margin of background."""
    im = Image.open(path).convert('RGB')
    box = ImageChops.difference(im, Image.new('RGB', im.size, im.getpixel((0, 0)))).getbbox()
    box = (max(box[0] - margin, 0), max(box[1] - margin, 0),
           min(box[2] + margin, im.width), min(box[3] + margin, im.height))
    im.crop(box).save(path, optimize=True)


with tempfile.TemporaryDirectory() as work:
    plates = os.path.join(work, 'plates.png')
    openscad(plates, '304,-330,520,304,-102,0', 'o', '4800,1700')
    crop(plates)
    os.replace(plates, os.path.join(HERE, 'plates.png'))
openscad(os.path.join(HERE, 'closeup.png'), '24,-74,50,24,-24,0', 'p', '1600,1000')
print('wrote plates.png and closeup.png')
