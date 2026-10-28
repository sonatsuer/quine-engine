// Empirical checks for the gnuplot QR quine. Needs gnuplot 6 with the png terminal.
//
//   node check.mjs [file.gp]    fuzz the encoder, then check the quine
//   node check.mjs --fuzz       fuzz the encoder only
//
// The default file is qr-code.gp in this folder, written by `lake exe quine`. Each file is plotted
// with gnuplot's png terminal at 740 x 740 pixels, where a module is exactly 4 pixels and the plot
// is the symbol with its 4-module quiet zone. The image is decoded with jsQR and with ZXing in
// pure-barcode mode.

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
const ENC = readFileSync(join(HERE, 'encoder.gp.inc'), 'latin1');
const CAPACITY = 2953;
const work = mkdtempSync(join(tmpdir(), 'gp-quine-'));

// Plot a gnuplot file to a PNG; returns null if gnuplot reports an error.
function render(gpPath) {
  const png = join(work, 'plot.png');
  try {
    execFileSync('gnuplot', ['-e', `set term png size 740,740; set output '${png}'`, gpPath],
      { stdio: ['ignore', 'ignore', 'ignore'] });
  } catch {
    return null;
  }
  return PNG.sync.read(readFileSync(png));
}

function decodeJsQR(img) {
  const r = jsQR(new Uint8ClampedArray(img.data), img.width, img.height);
  return r && String.fromCharCode(...r.binaryData);
}

function decodeZXing(img) {
  const lum = new Uint8ClampedArray(img.width * img.height);
  for (let i = 0; i < lum.length; i++) lum[i] = img.data[4 * i];
  const hints = new Map([[DecodeHintType.PURE_BARCODE, true], [DecodeHintType.CHARACTER_SET, 'ISO-8859-1']]);
  try {
    return new QRCodeReader().decode(new BinaryBitmap(new HybridBinarizer(new RGBLuminanceSource(lum, img.width, img.height))), hints).getText();
  } catch {
    return null;
  }
}

function check(label, gpPath, expected) {
  const img = render(gpPath);
  if (!img) throw new Error(`${label}: gnuplot failed`);
  const a = decodeJsQR(img), b = decodeZXing(img);
  if (a !== expected || b !== expected) {
    throw new Error(`${label}: decoded text differs (jsQR ${a === expected}, ZXing ${b === expected})`);
  }
}

// Lean's `quoteWith`: bind `t`, in octal escapes, to `v`, and evaluate `s=v;ENC`.
const octal = s => [...s].map(c => '\\' + c.charCodeAt(0).toString(8).padStart(3, '0')).join('');
const program = s => `v="${octal(s)}";eval 's=v;${ENC}'`;

function fuzz() {
  const lengths = [0, 1, 1000, CAPACITY - 1, CAPACITY];
  for (let r = 0; r < 6; r++) lengths.push(Math.floor(Math.random() * (CAPACITY + 1)));
  for (const len of lengths) {
    let s = '';
    for (let i = 0; i < len; i++) s += String.fromCharCode(32 + Math.floor(Math.random() * 95));
    const path = join(work, 'fuzz.gp');
    writeFileSync(path, program(s), 'latin1');
    check(`fuzz length ${len}`, path, s);
  }
  const path = join(work, 'over.gp');
  writeFileSync(path, program('x'.repeat(CAPACITY + 1)), 'latin1');
  if (render(path)) throw new Error('fuzz: the encoder accepted a text above capacity');
  console.log(`encoder: ${lengths.length} random texts decoded correctly by jsQR and ZXing; overflow rejected`);
}

function checkQuine(path) {
  const file = readFileSync(path, 'latin1');
  check(path, path, file);
  console.log(`${path}: ${file.length} bytes; gnuplot's plot decodes to the file itself (jsQR and ZXing)`);
}

try {
  const args = process.argv.slice(2);
  fuzz();
  if (!args.includes('--fuzz')) checkQuine(args.find(a => !a.startsWith('--')) ?? join(HERE, 'qr-code.gp'));
} finally {
  rmSync(work, { recursive: true, force: true });
}
