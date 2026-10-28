// Empirical checks for the PostScript color QR quine. Needs Ghostscript (`gs`).
//
//   node check.mjs [file.ps]    fuzz the encoder, then check the quine
//   node check.mjs --fuzz       fuzz the encoder only
//
// The default file is color-qr.ps in this folder, written by `lake exe quine`. Each file is
// rendered in color with Ghostscript at 216 dpi, where a module (3 points) is exactly 9 pixels.
// The page is split into its red, green and blue channels; each is a QR code. jsQR reads each
// whole channel; ZXing reads each channel cropped to the symbol's quiet zone, in pure-barcode mode.
// The three payloads are concatenated.

import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import jsQR from 'jsqr';
import { PNG } from 'pngjs';
import {
  BinaryBitmap, DecodeHintType, HybridBinarizer, QRCodeReader, RGBLuminanceSource,
} from '@zxing/library';

const HERE = new URL('.', import.meta.url).pathname;
const ENC = readFileSync(join(HERE, 'encoder.ps.inc'), 'latin1');
const DPI = 216;
const CAPACITY = 5520;
const SIZE = (141 + 8) * 3;   // the symbol with its quiet zone, in points
const work = mkdtempSync(join(tmpdir(), 'ps-color-quine-'));

// Render a PostScript file to an RGB PNG; returns null if Ghostscript reports an error.
function render(psPath) {
  const png = join(work, 'page.png');
  try {
    execFileSync('gs', ['-q', '-dSAFER', '-dBATCH', '-dNOPAUSE', '-sDEVICE=png16m', `-r${DPI}`,
      `-sOutputFile=${png}`, psPath], { stdio: ['ignore', 'ignore', 'ignore'] });
  } catch {
    return null;
  }
  return PNG.sync.read(readFileSync(png));
}

// Channel k of the page as a grayscale RGBA image.
function channel(img, k) {
  const px = new Uint8ClampedArray(img.data.length);
  for (let i = 0; i < img.width * img.height; i++) {
    const v = img.data[4 * i + k];
    px[4 * i] = px[4 * i + 1] = px[4 * i + 2] = v;
    px[4 * i + 3] = 255;
  }
  return { data: px, width: img.width, height: img.height };
}

function decodeJsQR(img) {
  const r = jsQR(img.data, img.width, img.height);
  return r && String.fromCharCode(...r.binaryData);
}

function decodeZXing(img) {
  const s = DPI / 72;
  const x0 = Math.round(20 * s), x1 = Math.round((20 + SIZE) * s);
  const y0 = Math.round(img.height - (140 + SIZE) * s), y1 = Math.round(img.height - 140 * s);
  const w = x1 - x0, h = y1 - y0, lum = new Uint8ClampedArray(w * h);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) lum[y * w + x] = img.data[((y + y0) * img.width + x + x0) * 4];
  const hints = new Map([[DecodeHintType.PURE_BARCODE, true], [DecodeHintType.CHARACTER_SET, 'ISO-8859-1']]);
  try {
    return new QRCodeReader().decode(new BinaryBitmap(new HybridBinarizer(new RGBLuminanceSource(lum, w, h))), hints).getText();
  } catch {
    return null;
  }
}

function check(label, psPath, expected) {
  const img = render(psPath);
  if (!img) throw new Error(`${label}: Ghostscript failed`);
  const parts = [0, 1, 2].map(k => channel(img, k));
  const a = parts.map(decodeJsQR), b = parts.map(decodeZXing);
  if (a.some(x => x === null) || a.join('') !== expected || b.some(x => x === null) || b.join('') !== expected) {
    throw new Error(`${label}: decoded text differs (jsQR ${a.join('') === expected}, ZXing ${b.join('') === expected})`);
  }
}

const hex = s => Buffer.from(s, 'latin1').toString('hex');
const program = s => `%!PS\n${ENC} <${hex(s)}> Q showpage\n`;

function fuzz() {
  const lengths = [0, 1, 2, 1000, CAPACITY - 1, CAPACITY];
  for (let r = 0; r < 5; r++) lengths.push(Math.floor(Math.random() * (CAPACITY + 1)));
  for (const len of lengths) {
    let s = '';
    for (let i = 0; i < len; i++) s += String.fromCharCode(32 + Math.floor(Math.random() * 95));
    const path = join(work, 'fuzz.ps');
    writeFileSync(path, program(s), 'latin1');
    check(`fuzz length ${len}`, path, s);
  }
  const path = join(work, 'over.ps');
  writeFileSync(path, program('x'.repeat(CAPACITY + 1)), 'latin1');
  if (render(path)) throw new Error('fuzz: the encoder accepted a text above capacity');
  console.log(`encoder: ${lengths.length} random texts decoded from the three channels by jsQR and ZXing; overflow rejected`);
}

function checkQuine(path) {
  const file = readFileSync(path, 'latin1');
  // Viewers built on libspectre (Xreader, Evince) refuse PostScript without a final newline.
  if (!file.endsWith('\n')) throw new Error(`${path}: the file does not end with a newline`);
  check(path, path, file);
  console.log(`${path}: ${file.length} bytes; Ghostscript's rendering decodes to the file itself, channel by channel (jsQR and ZXing)`);
}

try {
  const args = process.argv.slice(2);
  fuzz();
  if (!args.includes('--fuzz')) checkQuine(args.find(a => !a.startsWith('--')) ?? join(HERE, 'color-qr.ps'));
} finally {
  rmSync(work, { recursive: true, force: true });
}
