// Empirical checks for the color QR quine.
//
//   node check.mjs [file.svg] [--png shot.png]
//
// The default file is color-qr.svg in this folder, written by `lake exe quine`. A script is run in
// a sandbox whose `document` records the colored paths that `drawColorQR` draws. The picture is
// split into its red, green and blue channels; each channel is a QR code, decoded with jsQR and
// ZXing, and the three payloads are concatenated. With --png, a browser screenshot of the file is
// split and decoded in the same way (jsQR).

import { readFileSync } from 'node:fs';
import vm from 'node:vm';
import jsQR from 'jsqr';
import { PNG } from 'pngjs';
import {
  BinaryBitmap, DecodeHintType, HybridBinarizer, QRCodeReader, RGBLuminanceSource,
} from '@zxing/library';

const HERE = new URL('.', import.meta.url).pathname;
const ENC = readFileSync(HERE + 'drawcolor.js.inc', 'latin1');
const N = 141, CAPACITY = 5520;

// Run a script; return a map from "x,y" to the module's fill color ("#rgb", each digit 0 or f).
function draw(script, globals = {}) {
  const paths = [];
  const root = { namespaceURI: 'http://www.w3.org/2000/svg', style: {}, setAttribute() {}, append(el) { paths.push(el); } };
  const document = {
    documentElement: root,
    createElementNS: () => ({ attrs: {}, setAttribute(k, v) { this.attrs[k] = v; } }),
  };
  vm.runInNewContext(script, { document, ...globals });
  if (paths.length === 0) throw new Error('nothing was drawn');
  const color = new Map();
  for (const p of paths) for (const [, x, y] of p.attrs.d.matchAll(/M(\d+),(\d+)h1v1h-1/g)) color.set(`${x},${y}`, p.attrs.fill);
  return color;
}

// Channel k (0 red, 1 green, 2 blue) as a black-on-white raster with a 4-module quiet zone.
function channel(color, k, scale = 4) {
  const w = (N + 8) * scale, px = new Uint8ClampedArray(w * w * 4).fill(255);
  for (const [key, fill] of color) {
    if (fill[1 + k] !== '0') continue;
    const [x, y] = key.split(',').map(Number);
    for (let i = 0; i < scale; i++) for (let j = 0; j < scale; j++) {
      const o = (((y + 4) * scale + i) * w + (x + 4) * scale + j) * 4;
      px[o] = px[o + 1] = px[o + 2] = 0;
    }
  }
  return { px, w, h: w };
}

function decodeJsQR({ px, w, h }) {
  const r = jsQR(px, w, h);
  return r && String.fromCharCode(...r.binaryData);
}

function decodeZXing({ px, w, h }) {
  const lum = new Uint8ClampedArray(w * h);
  for (let i = 0; i < w * h; i++) lum[i] = px[4 * i];
  const hints = new Map([[DecodeHintType.PURE_BARCODE, true], [DecodeHintType.CHARACTER_SET, 'ISO-8859-1']]);
  try {
    return new QRCodeReader().decode(new BinaryBitmap(new HybridBinarizer(new RGBLuminanceSource(lum, w, h))), hints).getText();
  } catch {
    return null;
  }
}

function check(label, color, expected) {
  const parts = [0, 1, 2].map(k => channel(color, k));
  const a = parts.map(decodeJsQR), b = parts.map(decodeZXing);
  if (a.some(x => x === null) || a.join('') !== expected || b.some(x => x === null) || b.join('') !== expected) {
    throw new Error(`${label}: decoded text differs (jsQR ${a.join('') === expected}, ZXing ${b.join('') === expected})`);
  }
}

function fuzz() {
  const lengths = [0, 1, 2, 3, 1000, CAPACITY - 1, CAPACITY];
  for (let r = 0; r < 8; r++) lengths.push(Math.floor(Math.random() * (CAPACITY + 1)));
  for (const len of lengths) {
    let s = '';
    for (let i = 0; i < len; i++) s += String.fromCharCode(32 + Math.floor(Math.random() * 95));
    check(`fuzz length ${len}`, draw(`${ENC};drawColorQR(s)`, { s }), s);
  }
  let threw = false;
  try { draw(`${ENC};drawColorQR(s)`, { s: 'x'.repeat(CAPACITY + 1) }); } catch { threw = true; }
  if (!threw) throw new Error('fuzz: the encoder accepted a text above capacity');
  console.log(`encoder: ${lengths.length} random texts decoded from the three channels by jsQR and ZXing; overflow rejected`);
}

function checkQuine(path) {
  const file = readFileSync(path, 'latin1');
  const script = file.slice(file.indexOf('<script>') + 8, file.indexOf('</script>'));
  check(path, draw(script), file);
  console.log(`${path}: ${file.length} bytes; the three channels decode to the file itself (jsQR and ZXing)`);
  return file;
}

// Decode a browser screenshot channel by channel.
function checkScreenshot(png, file) {
  const img = PNG.sync.read(readFileSync(png));
  const parts = [0, 1, 2].map(k => {
    const px = new Uint8ClampedArray(img.data.length);
    for (let i = 0; i < img.width * img.height; i++) {
      const v = img.data[4 * i + k];
      px[4 * i] = px[4 * i + 1] = px[4 * i + 2] = v; px[4 * i + 3] = 255;
    }
    return decodeJsQR({ px, w: img.width, h: img.height });
  });
  if (parts.join('') !== file) throw new Error(`${png}: the screenshot does not decode to the file`);
  console.log(`${png}: the browser's rendering decodes to the file itself, channel by channel (jsQR)`);
}

const args = process.argv.slice(2);
fuzz();
const pngAt = args.indexOf('--png');
const svg = args.find((a, i) => !a.startsWith('--') && i !== pngAt + 1) ?? HERE + 'color-qr.svg';
const file = checkQuine(svg);
if (pngAt >= 0) checkScreenshot(args[pngAt + 1], file);
