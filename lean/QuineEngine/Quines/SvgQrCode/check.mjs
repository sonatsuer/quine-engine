// Empirical checks for the SVG QR quine.
//
//   node check.mjs [file.svg]                 fuzz the encoder, then check the quine
//   node check.mjs --fuzz                     fuzz the encoder only
//   node check.mjs [file.svg] --png shot.png  also decode a browser screenshot of the file
//
// The default file is qr-code.svg in this folder, written by `lake exe quine`.
//
// A script is run in a sandbox whose `document` records the path that `drawQR` draws. The path is
// rasterised and decoded with two independent decoders, jsQR and ZXing.

import { readFileSync } from 'node:fs';
import { PNG } from 'pngjs';
import vm from 'node:vm';
import jsQR from 'jsqr';
import { DOMParser } from '@xmldom/xmldom';
import {
  BinaryBitmap, HybridBinarizer, QRCodeReader, RGBLuminanceSource, DecodeHintType,
} from '@zxing/library';

const ENC = readFileSync(new URL('encoder.js', import.meta.url), 'utf8');

// Run `script` with a stub document and return the set of dark modules it draws.
function run(script, globals = {}) {
  let d = null;
  const root = {
    namespaceURI: 'http://www.w3.org/2000/svg',
    style: {},
    setAttribute() {},
    append(el) { d = el.d; },
  };
  const document = {
    documentElement: root,
    createElementNS: () => ({ setAttribute(k, v) { if (k === 'd') this.d = v; } }),
  };
  vm.runInNewContext(script, { document, ...globals });
  if (d === null) throw new Error('nothing was drawn');
  const dark = new Set();
  for (const [, x, y] of d.matchAll(/M(\d+),(\d+)h1v1h-1/g)) dark.add(`${x},${y}`);
  return dark;
}

// Rasterise modules (with a 4-module quiet zone) to RGBA, `scale` pixels per module.
function raster(dark, n = 141, scale = 4) {
  const w = (n + 8) * scale;
  const px = new Uint8ClampedArray(w * w * 4).fill(255);
  for (const key of dark) {
    const [x, y] = key.split(',').map(Number);
    for (let i = 0; i < scale; i++) for (let j = 0; j < scale; j++) {
      const o = (((y + 4) * scale + i) * w + (x + 4) * scale + j) * 4;
      px[o] = px[o + 1] = px[o + 2] = 0;
    }
  }
  return { px, w };
}

function decodeJsQR({ px, w }) {
  const r = jsQR(px, w, w);
  return r && String.fromCharCode(...r.binaryData);
}

function decodeZXing({ px, w }) {
  const lum = new Uint8ClampedArray(w * w);
  for (let i = 0; i < w * w; i++) lum[i] = px[4 * i];
  const bitmap = new BinaryBitmap(new HybridBinarizer(new RGBLuminanceSource(lum, w, w)));
  const hints = new Map([[DecodeHintType.PURE_BARCODE, true], [DecodeHintType.CHARACTER_SET, 'ISO-8859-1']]);
  return new QRCodeReader().decode(bitmap, hints).getText();
}

function check(label, script, expected, globals) {
  const img = raster(run(script, globals));
  const a = decodeJsQR(img);
  const b = decodeZXing(img);
  if (a !== expected || b !== expected) {
    throw new Error(`${label}: decoded text differs (jsQR ${a === expected}, ZXing ${b === expected})`);
  }
}

// Safe characters: printable ASCII except " \ < &.
const SAFE = [...Array(95)].map((_, i) => String.fromCharCode(32 + i)).filter(c => !'"\\<&'.includes(c));

function fuzz(rounds = 25) {
  const lengths = [0, 1, 2, 100, 1000, 1839, 1840];
  for (let r = 0; r < rounds; r++) lengths.push(Math.floor(Math.random() * 1841));
  for (const len of lengths) {
    let s = '';
    for (let i = 0; i < len; i++) s += SAFE[Math.floor(Math.random() * SAFE.length)];
    check(`fuzz length ${len}`, `${ENC};drawQR(s)`, s, { s });
  }
  let threw = false;
  try { run(`${ENC};drawQR(s)`, { s: 'x'.repeat(1841) }); } catch { threw = true; }
  if (!threw) throw new Error('fuzz: drawQR accepted a text above capacity');
  console.log(`encoder: ${lengths.length} random texts decoded correctly by jsQR and ZXing; overflow rejected`);
}

function checkQuine(path) {
  const file = readFileSync(path, 'latin1');
  let xmlError = null;
  const doc = new DOMParser({ onError: (level, msg) => { xmlError ??= `${level}: ${msg}`; } })
    .parseFromString(file, 'image/svg+xml');
  if (xmlError) throw new Error(`${path} is not well-formed XML (${xmlError})`);
  const script = doc.getElementsByTagName('script')[0].textContent;
  check(path, script, file);
  console.log(`${path}: ${file.length} bytes; its QR code decodes to the file itself (jsQR and ZXing)`);
  return file;
}

// Decode a screenshot (PNG) of the file as rendered by a real browser.
function checkScreenshot(png, file) {
  const img = PNG.sync.read(readFileSync(png));
  const r = jsQR(new Uint8ClampedArray(img.data), img.width, img.height);
  const text = r && String.fromCharCode(...r.binaryData);
  if (text !== file) throw new Error(`${png}: the screenshot does not decode to the file`);
  console.log(`${png}: the browser's rendering decodes to the file itself (jsQR)`);
}

const args = process.argv.slice(2);
fuzz();
if (!args.includes('--fuzz')) {
  const pngAt = args.indexOf('--png');
  const png = pngAt >= 0 ? args[pngAt + 1] : null;
  const svg = args.find((a, i) => !a.startsWith('--') && i !== pngAt + 1)
    ?? new URL('qr-code.svg', import.meta.url).pathname;
  const file = checkQuine(svg);
  if (png) checkScreenshot(png, file);
}
