// Empirical checks for the LaTeX color QR quine. Needs pdflatex (with expl3 and the cmmi/cmsy
// fonts) and pdftoppm (poppler), plus Node 18+.
//
//   node check.mjs [file.tex]    fuzz the encoder, then check the quine
//   node check.mjs --fuzz        fuzz the encoder only
//
// A file compiles to one page: three version-40 QR codes overlaid in the red, green and blue
// channels. The page is rendered twice. jsQR reads a 320-dpi anti-aliased rendering, where the
// tinted math symbols are present. ZXing reads a crisp 111-dpi rendering thresholded at 50%,
// about 4 pixels per module. Each channel is decoded as an ordinary QR code, and the three
// payloads are concatenated. Compiling takes about three minutes per file.

import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, join } from 'node:path';
import jsQR from 'jsqr';
import { PNG } from 'pngjs';
import {
  BinaryBitmap, DecodeHintType, HybridBinarizer, QRCodeReader, RGBLuminanceSource,
} from '@zxing/library';

const HERE = new URL('.', import.meta.url).pathname;
const read = name => readFileSync(join(HERE, name), 'latin1');
const PRE = read('pre.inc'), LIB = read('library.inc'), EPI = read('epilogue.inc');
const CAPACITY = 3 * 2953;
const work = mkdtempSync(join(tmpdir(), 'tex-quine-'));

// Compile a .tex file in the scratch directory; returns the PDF path, or null on error.
function compile(texPath) {
  try {
    execFileSync('pdflatex', ['-interaction=nonstopmode', '-halt-on-error',
      '-output-directory', work, texPath], { stdio: ['ignore', 'ignore', 'ignore'] });
  } catch {
    return null;
  }
  return join(work, basename(texPath).replace(/\.tex$/, '.pdf'));
}

function render(pdf, dpi, aa) {
  const out = join(work, 'page' + dpi);
  execFileSync('pdftoppm', ['-r', '' + dpi, '-png', '-aa', aa, '-aaVector', aa, '-singlefile',
    pdf, out]);
  return PNG.sync.read(readFileSync(out + '.png'));
}

// Channel k of an RGB image as a grey RGBA image, thresholded at 50% if `crisp`.
function channel(img, k, crisp) {
  const data = new Uint8ClampedArray(img.width * img.height * 4);
  for (let i = 0; i < img.width * img.height; i++) {
    let v = img.data[4 * i + k];
    if (crisp) v = v < 128 ? 0 : 255;
    data[4 * i] = data[4 * i + 1] = data[4 * i + 2] = v;
    data[4 * i + 3] = 255;
  }
  return { data, width: img.width, height: img.height };
}

function decodeJsQR(img) {
  const r = jsQR(img.data, img.width, img.height);
  return r ? String.fromCharCode(...r.binaryData) : null;
}

function decodeZXing(img) {
  const lum = new Uint8ClampedArray(img.width * img.height);
  for (let i = 0; i < lum.length; i++) lum[i] = img.data[4 * i];
  const hints = new Map([[DecodeHintType.PURE_BARCODE, true],
    [DecodeHintType.CHARACTER_SET, 'ISO-8859-1']]);
  try {
    const bitmap = new BinaryBitmap(new HybridBinarizer(
      new RGBLuminanceSource(lum, img.width, img.height)));
    return new QRCodeReader().decode(bitmap, hints).getText();
  } catch {
    return null;
  }
}

// Decode the three channels of a compiled page with both decoders; returns the concatenation.
function decode(label, pdf) {
  const hi = render(pdf, 320, 'yes'), lo = render(pdf, 111, 'no');
  let out = '';
  for (let k = 0; k < 3; k++) {
    const a = decodeJsQR(channel(hi, k, false)), b = decodeZXing(channel(lo, k, true));
    if (a === null || a !== b) {
      throw new Error(`${label}: channel ${'RGB'[k]} (jsQR ${a !== null}, ZXing ${b !== null})`);
    }
    out += a;
  }
  return out;
}

// A harness that draws the color QR code of `s`: the file's setup and library, then `s` as the
// rebuilt file in place of the template's first step, then the rest of the template.
function harness(s) {
  const setup = PRE.slice(0, PRE.indexOf('\\long\\def\\grab'));
  const chars = [...s].map(c => `\\char_generate:nn{${c.charCodeAt(0)}}{12}`);
  const lines = [];
  for (let i = 0; i < chars.length; i += 100) lines.push(chars.slice(i, i + 100).join(''));
  const rest = EPI.slice(EPI.indexOf('}}') + 2);
  return `${setup}\n${LIB}\n\\tl_set:Nx\\Vf{\n${lines.join('\n')}\n}${rest}\\end{document}\n`;
}

function fuzz() {
  const lengths = [0, 1, CAPACITY - 1, CAPACITY, Math.floor(Math.random() * (CAPACITY + 1))];
  for (const len of lengths) {
    let s = '';
    for (let i = 0; i < len; i++) s += String.fromCharCode(32 + Math.floor(Math.random() * 95));
    const path = join(work, 'fuzz.tex');
    writeFileSync(path, harness(s), 'latin1');
    const pdf = compile(path);
    if (!pdf) throw new Error(`fuzz length ${len}: pdflatex failed`);
    if (decode(`fuzz length ${len}`, pdf) !== s) {
      throw new Error(`fuzz length ${len}: decoded text differs`);
    }
  }
  const over = join(work, 'over.tex');
  writeFileSync(over, harness('x'.repeat(CAPACITY + 1)), 'latin1');
  if (compile(over)) throw new Error('fuzz: the encoder accepted a text above capacity');
  console.log(`encoder: ${lengths.length} random texts up to ${CAPACITY} bytes decoded from ` +
    'the three channels by jsQR and ZXing; overflow rejected');
}

function checkQuine(texPath) {
  const file = readFileSync(texPath, 'latin1');
  const pdf = compile(texPath);
  if (!pdf) throw new Error(`${texPath}: pdflatex failed`);
  if (decode(texPath, pdf) !== file) throw new Error(`${texPath}: decoded text differs`);
  console.log(`${texPath}: ${file.length} bytes; the three channels decode to the file itself ` +
    '(jsQR and ZXing)');
}

try {
  const args = process.argv.slice(2);
  fuzz();
  if (!args.includes('--fuzz')) {
    checkQuine(args.find(a => !a.startsWith('--')) ?? join(HERE, 'qr-code.tex'));
  }
} finally {
  rmSync(work, { recursive: true, force: true });
}
