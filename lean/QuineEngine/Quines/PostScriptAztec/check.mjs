// Empirical checks for the PostScript Aztec quine. Needs Ghostscript (`gs`).
//
//   node check.mjs [file.ps]    fuzz the encoder, then check the quine
//   node check.mjs --fuzz       fuzz the encoder only
//
// The default file is aztec.ps in this folder, written by `lake exe quine`. Each file is rendered
// with Ghostscript at 216 dpi, where a module (3 points) is exactly 9 pixels, and the page is
// decoded with ZXing's Aztec reader. (jsQR reads only QR codes, so ZXing is the one independent
// Aztec decoder here.)

import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { PNG } from 'pngjs';
import {
  AztecCodeReader, BinaryBitmap, DecodeHintType, HybridBinarizer, RGBLuminanceSource,
} from '@zxing/library';

const HERE = new URL('.', import.meta.url).pathname;
const ENC = readFileSync(join(HERE, 'encoder.ps.inc'), 'latin1');
const DPI = 216;
const CAPACITY = 2278;
const work = mkdtempSync(join(tmpdir(), 'ps-aztec-quine-'));

// Render a PostScript file to a grayscale PNG; returns null if Ghostscript reports an error.
function render(psPath) {
  const png = join(work, 'page.png');
  try {
    execFileSync('gs', ['-q', '-dSAFER', '-dBATCH', '-dNOPAUSE', '-sDEVICE=pnggray', `-r${DPI}`,
      `-sOutputFile=${png}`, psPath], { stdio: ['ignore', 'ignore', 'ignore'] });
  } catch {
    return null;
  }
  return PNG.sync.read(readFileSync(png));
}

function decode(img) {
  const lum = new Uint8ClampedArray(img.width * img.height);
  for (let i = 0; i < lum.length; i++) lum[i] = img.data[4 * i];
  const hints = new Map([[DecodeHintType.CHARACTER_SET, 'ISO-8859-1']]);
  try {
    return new AztecCodeReader().decode(new BinaryBitmap(new HybridBinarizer(new RGBLuminanceSource(lum, img.width, img.height))), hints).getText();
  } catch {
    return null;
  }
}

function check(label, psPath, expected) {
  const img = render(psPath);
  if (!img) throw new Error(`${label}: Ghostscript failed`);
  if (decode(img) !== expected) throw new Error(`${label}: decoded text differs`);
}

const hex = s => Buffer.from(s, 'latin1').toString('hex');
const program = s => `%!PS\n${ENC} <${hex(s)}> Q showpage\n`;

function fuzz() {
  const lengths = [0, 1, 31, 32, 2078, 2079, CAPACITY - 1, CAPACITY];
  for (let r = 0; r < 6; r++) lengths.push(Math.floor(Math.random() * (CAPACITY + 1)));
  for (const len of lengths) {
    let s = '';
    for (let i = 0; i < len; i++) s += String.fromCharCode(32 + Math.floor(Math.random() * 95));
    const path = join(work, 'fuzz.ps');
    writeFileSync(path, program(s), 'latin1');
    check(`fuzz length ${len}`, path, s);
  }
  // Over 2486 bytes cannot fit 32 layers with 3 error-correction codewords, whatever the stuffing.
  const over = join(work, 'over.ps');
  writeFileSync(over, program('x'.repeat(2500)), 'latin1');
  if (render(over)) throw new Error('fuzz: the encoder accepted a text that cannot fit');
  console.log(`encoder: ${lengths.length} random texts decoded by ZXing's Aztec reader; overflow rejected`);
}

function checkQuine(path) {
  const file = readFileSync(path, 'latin1');
  // Viewers built on libspectre (Xreader, Evince) refuse PostScript without a final newline.
  if (!file.endsWith('\n')) throw new Error(`${path}: the file does not end with a newline`);
  check(path, path, file);
  console.log(`${path}: ${file.length} bytes; Ghostscript's rendering decodes to the file itself (ZXing)`);
}

try {
  const args = process.argv.slice(2);
  fuzz();
  if (!args.includes('--fuzz')) checkQuine(args.find(a => !a.startsWith('--')) ?? join(HERE, 'aztec.ps'));
} finally {
  rmSync(work, { recursive: true, force: true });
}
