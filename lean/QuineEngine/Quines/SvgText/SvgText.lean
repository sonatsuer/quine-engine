import QuineEngine.Engine
import QuineEngine.SvgScript

/-!
# An SVG file that draws its own source text

The file has the shape of `QuineEngine.SvgScript`, and its evaluated code is `ENC;drawText(E)`,
where `ENC` is the JavaScript renderer in `drawtext.js.inc`. Displaying the file means drawing the
value of `E` as pixels: each character is a 5×7 glyph from `font5x7.txt` (the public-domain X11
misc-fixed font) in a 6×8 cell, 80 characters per row.

Scanning reads the pixels back cell by cell with the same font. So the retract is formal: Lean
proves that scanning inverts typesetting (`decode_typeset`), and no external decoder is trusted.
What is trusted is that the JavaScript renderer draws exactly `typeset`; `check.mjs` tests this.
-/

namespace QuineEngine.SvgText

open QuineEngine.SvgScript

/-! ## The font -/

/-- Each line of `font5x7.txt` is a hex character code and seven rows of `#` and `.`. -/
def fontSrc : String := include_str "font5x7.txt"

def splitOn (sep : Char) : Text → List Text
  | [] => [[]]
  | c :: r =>
    if c = sep then [] :: splitOn sep r
    else match splitOn sep r with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

def rowBits : Nat → Text → Nat
  | _, [] => 0
  | col, ch :: r => (if ch = '#' then 2 ^ col else 0) + rowBits (col + 1) r

/-- Bit `5 * r + c` is pixel `(c, r)` of the glyph, with `r` counted from the top. -/
def glyphBits : Nat → List Text → Nat
  | _, [] => 0
  | r, row :: rows => rowBits 0 row * 2 ^ (5 * r) + glyphBits (r + 1) rows

def fontEntries : List (Nat × Nat) :=
  (splitOn '\n' fontSrc.toList).filterMap fun line =>
    match splitOn ' ' line with
    | [[h1, h2], r1, r2, r3, r4, r5, r6, r7] =>
      match hexVal h1, hexVal h2 with
      | some a, some b => some (16 * a + b, glyphBits 0 [r1, r2, r3, r4, r5, r6, r7])
      | _, _ => none
    | _ => none

/-- The glyph of a character, as a 35-bit number; 0 (blank) for characters without a glyph. -/
def glyph (c : Char) : Nat := ((fontEntries.find? (·.1 == c.toNat)).map (·.2)).getD 0

def gbit (g r c : Nat) : Bool := g / 2 ^ (5 * r + c) % 2 == 1

def printable (c : Char) : Bool := 32 ≤ c.toNat && c.toNat < 127

/-- The 95 printable ASCII characters, space first. -/
def printables : Text := (List.range 95).map fun i => Char.ofNat (32 + i)

/-- The character whose glyph is `g`, or `?`. -/
def decodeGlyph (g : Nat) : Char :=
  (printables.find? fun c => (List.range 35).all fun k =>
    gbit g (k / 5) (k % 5) == gbit (glyph c) (k / 5) (k % 5)).getD '?'

theorem decodeGlyph_glyph : ∀ c ∈ printables, decodeGlyph (glyph c) = c := by decide +kernel

theorem decodeGlyph_zero : decodeGlyph 0 = ' ' := by decide +kernel

theorem mem_printables {c : Char} (h : printable c = true) : c ∈ printables := by
  simp only [printable, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [printables, List.mem_map, List.mem_range]
  exact ⟨c.toNat - 32, by omega, by
    rw [show 32 + (c.toNat - 32) = c.toNat by omega, Char.ofNat_toNat]⟩

/-! ## Bitmaps, typesetting and scanning -/

structure Bitmap where
  w : Nat
  h : Nat
  px : Nat → Nat → Bool

/-- Characters per row. -/
def W : Nat := 80

/-- The glyph in cell `i`: that of the `i`-th character, or blank past the end. -/
def cellGlyph (t : Text) (i : Nat) : Nat := ((t[i]?).map glyph).getD 0

/-- Typesetting: the rendering map. Character `i` is in cell `(i % W, i / W)`. -/
def typeset (t : Text) : Bitmap where
  w := 6 * W
  h := 8 * ((t.length + W - 1) / W)
  px X Y := decide (X / 6 < W) && decide (X % 6 < 5) && decide (Y % 8 < 7) &&
    gbit (cellGlyph t (Y / 8 * W + X / 6)) (Y % 8) (X % 6)

/-- Read cell `i` of a bitmap. -/
def decodeCell (b : Bitmap) (i : Nat) : Char :=
  (printables.find? fun c => (List.range 35).all fun k =>
    b.px (i % (b.w / 6) * 6 + k % 5) (i / (b.w / 6) * 8 + k / 5) ==
      gbit (glyph c) (k / 5) (k % 5)).getD '?'

def stripSpaces (l : Text) : Text := (l.reverse.dropWhile (· == ' ')).reverse

/-- Scanning: read every cell, row by row, and drop trailing spaces. -/
def decode (b : Bitmap) : Text := stripSpaces ((List.range (b.w / 6 * (b.h / 8))).map (decodeCell b))

/-- Texts that typesetting represents faithfully: nonempty, printable, not ending in a space. -/
def wf (t : Text) : Bool := !t.isEmpty && t.all printable && t.getLast? != some ' '

theorem typeset_cell (t : Text) {i k : Nat} (hk : k < 35) :
    (typeset t).px (i % W * 6 + k % 5) (i / W * 8 + k / 5) =
      gbit (cellGlyph t i) (k / 5) (k % 5) := by
  have h1 : (i % W * 6 + k % 5) / 6 = i % W := by unfold W; omega
  have h2 : (i % W * 6 + k % 5) % 6 = k % 5 := by omega
  have h3 : (i / W * 8 + k / 5) / 8 = i / W := by omega
  have h4 : (i / W * 8 + k / 5) % 8 = k / 5 := by omega
  have h5 : i / W * W + i % W = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i W
  have h6 : i % W < W := Nat.mod_lt _ (by unfold W; decide)
  simp [typeset, h1, h2, h3, h4, h5, h6, show k % 5 < 5 by omega, show k / 5 < 7 by omega]

theorem decodeCell_typeset (t : Text) (i : Nat) :
    decodeCell (typeset t) i = decodeGlyph (cellGlyph t i) := by
  have hw : (typeset t).w / 6 = W := by simp [typeset]
  unfold decodeCell decodeGlyph
  rw [hw]
  congr 2
  funext c
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor <;> intro h k hk <;> have := h k hk
  · rwa [typeset_cell t hk] at this
  · rwa [typeset_cell t hk]

theorem cellGlyph_decode {t : Text} (ht : t.all printable = true) (i : Nat) :
    decodeGlyph (cellGlyph t i) = (t[i]?).getD ' ' := by
  unfold cellGlyph
  cases h : t[i]? with
  | none => simpa using decodeGlyph_zero
  | some c =>
    have hc : c ∈ t := List.mem_of_getElem? h
    simpa using decodeGlyph_glyph c (mem_printables (List.all_eq_true.1 ht c hc))

theorem range_map_getD (t : Text) (N : Nat) (hN : t.length ≤ N) :
    (List.range N).map (fun i => (t[i]?).getD ' ') = t ++ List.replicate (N - t.length) ' ' := by
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    rw [List.getElem_map, List.getElem_range, List.getElem_append]
    split
    · rename_i h
      simp [List.getElem?_eq_getElem h]
    · rename_i h
      simp [List.getElem?_eq_none (by omega : t.length ≤ n)]

theorem dropWhile_replicate (n : Nat) (l : Text) :
    (List.replicate n ' ' ++ l).dropWhile (· == ' ') = l.dropWhile (· == ' ') := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.cons_append, List.dropWhile_cons_of_pos rfl, ih]

theorem stripSpaces_append (t : Text) (n : Nat) (ht : t.getLast? ≠ some ' ') :
    stripSpaces (t ++ List.replicate n ' ') = t := by
  unfold stripSpaces
  rw [List.reverse_append, List.reverse_replicate, dropWhile_replicate]
  have hr : t.reverse.dropWhile (· == ' ') = t.reverse := by
    cases h : t.reverse with
    | nil => rfl
    | cons a r =>
      have ha : t.getLast? = some a := by rw [← List.head?_reverse, h]; rfl
      have : a ≠ ' ' := fun e => ht (by rw [ha, e])
      simp [this]
  rw [hr, List.reverse_reverse]

theorem wf_iff (t : Text) :
    wf t = true ↔ t ≠ [] ∧ t.all printable = true ∧ t.getLast? ≠ some ' ' := by
  simp [wf, and_assoc]

/-- Scanning inverts typesetting on well-formed texts. -/
theorem decode_typeset {t : Text} (h : wf t = true) : decode (typeset t) = t := by
  obtain ⟨-, hp, hl⟩ := (wf_iff t).1 h
  have hf : decodeCell (typeset t) = fun i => (t[i]?).getD ' ' :=
    funext fun i => by rw [decodeCell_typeset, cellGlyph_decode hp]
  have hw : (typeset t).w / 6 = W := by simp [typeset]
  have hh : (typeset t).h / 8 = (t.length + W - 1) / W := by simp [typeset]
  have hN : t.length ≤ W * ((t.length + W - 1) / W) := by unfold W; omega
  unfold decode
  rw [hf, hw, hh, range_map_getD t _ hN, stripSpaces_append t _ hl]

theorem all256_of_wf {t : Text} (h : wf t = true) : t.all (·.toNat < 256) = true := by
  obtain ⟨-, hp, -⟩ := (wf_iff t).1 h
  simp only [List.all_eq_true, decide_eq_true_eq] at hp ⊢
  intro c hc
  have := hp c hc
  simp only [printable, Bool.and_eq_true, decide_eq_true_eq] at this
  omega

/-! ## The evaluated code -/

/-- The JavaScript renderer. It defines `H = String.fromCharCode` and `drawText`. -/
def ENC : Text := (include_str "drawtext.js.inc").toList

/-- The prefix of evaluated code: the renderer, then `;drawText(`. -/
def cpre : Text := ENC ++ ";drawText(".toList

def code (e : Expr) : Text := codeWith cpre e

def parseCode (c : Text) : Option Expr := parseCodeWith cpre c

/-! ## The representation system -/

def render (t : Text) : Bitmap ⊕ Text := if wf t then .inl (typeset t) else .inr t

def scan : Bitmap ⊕ Text → Option Text
  | .inl b => some (decode b)
  | .inr t => some t

/-- A file draws the value of `E` as text, when it has the expected shape and the value is well
formed. -/
def Disp (f : Text) (p : Bitmap ⊕ Text) : Prop :=
  ∃ x c e, parseFile f = some (x, c) ∧ parseCode c = some e ∧ wf (e.eval x) = true ∧
    p = .inl (typeset (e.eval x))

def system : System Text (Bitmap ⊕ Text) where
  disp := Disp
  scan := scan
  render := render
  scan_render t := by
    unfold render
    split
    · simp [scan, decode_typeset ‹_›]
    · rfl

/-! ## Quotation and the template -/

/-- The code `ENC;drawText(v)`. -/
def SHOW : Text := showWith cpre

def quote (t : Text) : Text := quoteWith cpre t

theorem safe_SHOW : safe SHOW = true := by decide +kernel

theorem parseCode_SHOW : parseCode SHOW = some .var := by decide +kernel

theorem parseFile_quote (t : Text) (ht : t.all (·.toNat < 256) = true) :
    parseFile (quote t) = some (t, SHOW) :=
  parseFile_quoteWith cpre safe_SHOW t ht

def quotation : Quotation system where
  Dom t := wf t = true
  q := quote
  disp_q t ht := ⟨.inl (typeset t), ⟨t, SHOW, .var, parseFile_quote t (all256_of_wf ht),
    parseCode_SHOW, ht, rfl⟩, by simp [system, render, ht]⟩

def tmpl : Text := code tmplExpr

theorem safe_tmpl : safe tmpl = true := by decide +kernel

theorem parseCode_tmpl : parseCode tmpl = some tmplExpr := by decide +kernel

def diagonal : Diagonal system quotation where
  sub := sub
  a := tmpl
  Ok x := safe x = true
  spec := by
    intro x hx s ⟨p, ⟨x', c', e', hf, hc, hw, hp⟩, hs⟩
    change parseFile (quote (sub x x)) = _ at hf
    rw [parseFile_quote _ (all256_sub hx)] at hf
    cases hf
    rw [parseCode_SHOW] at hc
    cases hc
    simp only [Expr.eval] at hw hp
    subst hp
    change some (decode (typeset (sub x x))) = some s at hs
    rw [decode_typeset hw, Option.some.injEq] at hs
    subst hs
    refine ⟨.inl (typeset (sub x x)), ⟨x, tmpl, tmplExpr, parseFile_sub safe_tmpl hx,
      parseCode_tmpl, by rw [eval_tmpl]; exact hw, by rw [eval_tmpl]⟩, ?_⟩
    change some (decode (typeset (sub x x))) = _
    rw [decode_typeset hw]

/-- The engine's output: an SVG file that draws its own source text. -/
def quine : Text := sub tmpl tmpl

theorem wf_quine : wf quine = true := by decide +kernel

theorem quine_correct : system.IsQuine quine :=
  diagonal.isQuine safe_tmpl wf_quine

end QuineEngine.SvgText
