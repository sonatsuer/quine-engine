// Empirical checks for the SVG text quine (Node.js 18 or later, no packages).
//
//   node check.mjs [file.svg]
//
// The default file is text.svg in this folder, written by `lake exe quine`. A script is run in a
// sandbox whose `document` records the path that `drawText` draws, and the path is turned back
// into pixels. The checks:
//   1. for random texts, drawText draws exactly the reference typesetting computed here from
//      font5x7.txt (5x7 glyphs in 6x8 cells, 80 characters per row);
//   2. the drawing of the file equals expected.pbm, Lean's own typesetting of the quine;
//   3. reading the drawing back with the font gives the file, character for character.

import { readFileSync } from 'node:fs';
import vm from 'node:vm';

const HERE = new URL('.', import.meta.url).pathname;
const ENC = readFileSync(HERE + 'drawtext.js.inc', 'latin1');
const W = 80;

const font = new Map();   // character -> 35 characters of '#' and '.', rows from the top
for (const line of readFileSync(HERE + 'font5x7.txt', 'utf8').trim().split('\n')) {
  const [hex, ...rows] = line.split(' ');
  font.set(String.fromCharCode(parseInt(hex, 16)), rows.join(''));
}
const byGlyph = new Map([...font].map(([c, g]) => [g, c]));

// Run a script; return the drawn pixels ("x,y" strings) and the viewBox size.
function draw(script, globals = {}) {
  let d = null, box = null;
  const root = {
    namespaceURI: 'http://www.w3.org/2000/svg', style: {},
    setAttribute(k, v) { if (k === 'viewBox') box = v.split(' ').map(Number); },
    append(el) { d = el.d; },
  };
  const document = {
    documentElement: root,
    createElementNS: () => ({ setAttribute(k, v) { if (k === 'd') this.d = v; } }),
  };
  vm.runInNewContext(script, { document, atob, ...globals });
  if (d === null) throw new Error('nothing was drawn');
  const px = new Set();
  for (const [, x, y] of d.matchAll(/M(\d+),(\d+)h1v1h-1/g)) px.add(`${x},${y}`);
  return { px, w: box[2], h: box[3] };
}

function typeset(s) {
  const px = new Set();
  [...s].forEach((ch, i) => {
    const g = font.get(ch);
    for (let k = 0; k < 35; k++) if (g[k] === '#') px.add(`${(i % W) * 6 + (k % 5)},${Math.floor(i / W) * 8 + Math.floor(k / 5)}`);
  });
  return { px, w: 6 * W, h: 8 * Math.ceil(s.length / W) };
}

function read({ px, w, h }) {
  let text = '';
  for (let i = 0; i < (w / 6) * (h / 8); i++) {
    let g = '';
    for (let k = 0; k < 35; k++) g += px.has(`${(i % (w / 6)) * 6 + (k % 5)},${Math.floor(i / (w / 6)) * 8 + Math.floor(k / 5)}`) ? '#' : '.';
    text += byGlyph.get(g) ?? '?';
  }
  return text.replace(/ +$/, '');
}

const same = (a, b) => a.w === b.w && a.h === b.h && a.px.size === b.px.size && [...a.px].every(p => b.px.has(p));

function readPbm(path) {
  const [magic, w, h, ...rows] = readFileSync(path, 'utf8').trim().split(/\s+/);
  if (magic !== 'P1') throw new Error('expected a plain PBM');
  const px = new Set();
  rows.join('').split('').forEach((b, k) => { if (b === '1') px.add(`${k % +w},${Math.floor(k / +w)}`); });
  return { px, w: +w, h: +h };
}

function fuzz(rounds = 40) {
  for (let r = 0; r < rounds; r++) {
    const len = 1 + Math.floor(Math.random() * 400);
    let s = '';
    for (let i = 0; i < len; i++) s += String.fromCharCode(32 + Math.floor(Math.random() * 95));
    s = s.replace(/ +$/, '') + 'x';
    if (!same(draw(`${ENC};drawText(s)`, { s }), typeset(s))) throw new Error(`fuzz: drawing differs for ${JSON.stringify(s)}`);
  }
  console.log(`renderer: ${rounds} random texts drawn exactly as the reference typesetting`);
}

function checkQuine(path) {
  const file = readFileSync(path, 'latin1');
  const script = file.slice(file.indexOf('<script>') + 8, file.indexOf('</script>'));
  const drawing = draw(script);
  if (!same(drawing, readPbm(HERE + 'expected.pbm'))) throw new Error(`${path}: the drawing differs from expected.pbm`);
  console.log(`${path}: the drawing equals expected.pbm (${drawing.w}x${drawing.h} pixels)`);
  if (read(drawing) !== file) throw new Error(`${path}: reading the drawing back does not give the file`);
  console.log(`${path}: reading the drawing back gives the file (${file.length} characters)`);
}

fuzz();
checkQuine(process.argv[2] ?? HERE + 'text.svg');
