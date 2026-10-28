// Empirical checks for the SVG Aztec quine.
//
//   node check.mjs [file.svg] [--png shot.png]
//
// The default file is aztec.svg in this folder, written by `lake exe quine`. A script is run in a
// sandbox whose `document` records the path that `drawAztec` draws; the path is rasterised and
// decoded with ZXing's Aztec reader. (jsQR reads only QR codes, so ZXing is the one independent
// Aztec decoder here.) With --png, a browser screenshot of the file is decoded as well.

import { readFileSync } from 'node:fs';
import vm from 'node:vm';
import { PNG } from 'pngjs';
import {
  AztecCodeReader, BinaryBitmap, DecodeHintType, HybridBinarizer, RGBLuminanceSource,
} from '@zxing/library';

const HERE = new URL('.', import.meta.url).pathname;
const ENC = readFileSync(HERE + 'drawaztec.js.inc', 'latin1');
const N = 151, CAPACITY = 2278;

function draw(script, globals = {}) {
  let d = null;
  const root = { namespaceURI: 'http://www.w3.org/2000/svg', style: {}, setAttribute() {}, append(el) { d = el.d; } };
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

function decode(lum, w, h) {
  const hints = new Map([[DecodeHintType.CHARACTER_SET, 'ISO-8859-1']]);
  try {
    return new AztecCodeReader().decode(new BinaryBitmap(new HybridBinarizer(new RGBLuminanceSource(lum, w, h))), hints).getText();
  } catch {
    return null;
  }
}

// Rasterise modules with a 4-module quiet zone and decode.
function decodeModules(dark, scale = 4) {
  const w = (N + 8) * scale, lum = new Uint8ClampedArray(w * w).fill(255);
  for (const key of dark) {
    const [x, y] = key.split(',').map(Number);
    for (let i = 0; i < scale; i++) for (let j = 0; j < scale; j++) lum[((y + 4) * scale + i) * w + (x + 4) * scale + j] = 0;
  }
  return decode(lum, w, w);
}

function fuzz() {
  const lengths = [0, 1, 2, 31, 32, 2078, 2079, CAPACITY - 1, CAPACITY];
  for (let r = 0; r < 10; r++) lengths.push(Math.floor(Math.random() * (CAPACITY + 1)));
  for (const len of lengths) {
    let s = '';
    for (let i = 0; i < len; i++) s += String.fromCharCode(32 + Math.floor(Math.random() * 95));
    if (decodeModules(draw(`${ENC};drawAztec(s)`, { s })) !== s) throw new Error(`fuzz: length ${len} does not decode`);
  }
  // Over 2486 bytes cannot fit 32 layers with 3 error-correction codewords, whatever the stuffing.
  let threw = false;
  try { draw(`${ENC};drawAztec(s)`, { s: 'x'.repeat(2500) }); } catch { threw = true; }
  if (!threw) throw new Error('fuzz: the encoder accepted a text that cannot fit');
  console.log(`encoder: ${lengths.length} random texts decoded by ZXing's Aztec reader; overflow rejected`);
}

function checkQuine(path) {
  const file = readFileSync(path, 'latin1');
  const script = file.slice(file.indexOf('<script>') + 8, file.indexOf('</script>'));
  if (decodeModules(draw(script)) !== file) throw new Error(`${path}: the Aztec code does not decode to the file`);
  console.log(`${path}: ${file.length} bytes; its Aztec code decodes to the file itself (ZXing)`);
  return file;
}

function checkScreenshot(png, file) {
  const img = PNG.sync.read(readFileSync(png));
  const lum = new Uint8ClampedArray(img.width * img.height);
  for (let i = 0; i < lum.length; i++) lum[i] = img.data[4 * i];
  if (decode(lum, img.width, img.height) !== file) throw new Error(`${png}: the screenshot does not decode to the file`);
  console.log(`${png}: the browser's rendering decodes to the file itself (ZXing)`);
}

const args = process.argv.slice(2);
fuzz();
const pngAt = args.indexOf('--png');
const svg = args.find((a, i) => !a.startsWith('--') && i !== pngAt + 1) ?? HERE + 'aztec.svg';
const file = checkQuine(svg);
if (pngAt >= 0) checkScreenshot(args[pngAt + 1], file);
