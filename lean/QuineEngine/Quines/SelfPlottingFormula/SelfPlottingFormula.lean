import QuineEngine.Engine

/-!
# A formula that plots itself

A formula is a two-line text
```
0<E,k=
78531…
```
where `E` is an arithmetic term in `x`, `y` and `k` over the natural numbers (`+ - * / % ^`, with
truncated subtraction and floor division), and the second line is the decimal value of `k`. It
denotes the set of points `(x, y) ∈ ℕ²` with `0 < E(x, y, k)`.

Pictures are compared with texts by typesetting: each character is a 3×5 glyph (from `font.txt`)
in a 4×6 cell, the two lines are right-aligned at column `W`, line 0 is the bottom line, and `y`
points up. The engine produces a formula whose solution set is exactly the typesetting of its own
text, constant included.
-/

namespace QuineEngine.SelfPlottingFormula

abbrev Text := List Char

/-! ## The alphabet and the font -/

/-- The characters of formulas, in the order of `font.txt`. Character `c` has code
`alphabet.idxOf c + 1`; code 0 is the blank glyph. Digits come first, so `'0'` has code 1. -/
def alphabet : Text := "0123456789+-*/%^()<=,xyk".toList

def code (c : Char) : Nat := alphabet.idxOf c + 1

/-- Each line of `font.txt` is a character followed by five rows of `#` and `.`, top row first. -/
def fontSrc : String := include_str "font.txt"

def splitOn (sep : Char) : Text → List Text
  | [] => [[]]
  | c :: r =>
    if c = sep then [] :: splitOn sep r
    else match splitOn sep r with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

def fontEntries : List (Char × List Text) :=
  (splitOn '\n' fontSrc.toList).filterMap fun line =>
    match splitOn ' ' line with
    | [[c], r1, r2, r3, r4, r5] => some (c, [r1, r2, r3, r4, r5])
    | _ => none

def rowBits : Nat → Text → Nat
  | _, [] => 0
  | col, ch :: r => (if ch = '#' then 2 ^ col else 0) + rowBits (col + 1) r

/-- Row `i` (counted from the top) of a glyph is cell row `4 - i` (counted from the bottom). -/
def glyphBits : Nat → List Text → Nat
  | _, [] => 0
  | i, row :: rows => rowBits 0 row * 2 ^ (4 * (4 - i)) + glyphBits (i + 1) rows

/-- The font as one number: bit `24 * code c + 4 * r + col` is pixel `(col, r)` of the glyph of
`c`, with `r` counted from the bottom of the 4×6 cell. -/
def F : Nat := (fontEntries.map fun (c, rows) => glyphBits 0 rows * 2 ^ (24 * code c)).sum

/-- Pixel `i = 4 * r + col` of the glyph with code `d`. -/
def bitN (d i : Nat) : Nat := F / 2 ^ (24 * d + i) % 2

/-- The width of the text block, in cells. -/
def W : Nat := 484

/-! ## Texts -/

def splitLines (t : Text) : Text × Text :=
  (t.takeWhile (· != '\n'), (t.dropWhile (· != '\n')).drop 1)

/-- A line that can be typeset: nonempty, alphabet characters only, at most `W` characters. -/
def good (s : Text) : Bool := !s.isEmpty && s.all (fun c => alphabet.elem c) && decide (s.length ≤ W)

/-- A well-formed text: two good lines. -/
def wf (t : Text) : Bool :=
  decide ((splitLines t).1 ++ '\n' :: (splitLines t).2 = t) && good (splitLines t).1 &&
    good (splitLines t).2

/-- The code in cell `p` of a line, counted from the right; 0 beyond the line's start. -/
def cellCode (s : Text) (p : Nat) : Nat := ((s.reverse[p]?).map code).getD 0

abbrev Pic := Nat → Nat → Bool

def typesetLines (top bot : Text) : Pic := fun X Y =>
  decide (Y / 6 ≤ 1) && decide (X / 4 < W) &&
    bitN (cellCode (if Y / 6 = 1 then top else bot) (W - 1 - X / 4)) (4 * (Y % 6) + X % 4) == 1

/-- Typesetting: the rendering map on well-formed texts. -/
def typeset (t : Text) : Pic := typesetLines (splitLines t).1 (splitLines t).2

/-- The character whose glyph is the glyph with code `d`, if any. -/
def decodeCode (d : Nat) : Option Char :=
  alphabet.find? fun c => (List.range 24).all fun i => bitN d i == bitN (code c) i

def decodeCell (pic : Pic) (L p : Nat) : Option Char :=
  alphabet.find? fun c => (List.range 24).all fun i =>
    pic (4 * (W - 1 - p) + i % 4) (6 * L + i / 4) == (bitN (code c) i == 1)

def decodeLine (pic : Pic) (L : Nat) : Text :=
  (List.range W).reverse.filterMap (decodeCell pic L)

/-- Scanning: read both lines, left to right, skipping blank cells. -/
def decode (pic : Pic) : Text := decodeLine pic 1 ++ '\n' :: decodeLine pic 0

/-! ### Facts about the font, checked by computation -/

theorem code_bounds : ∀ c ∈ alphabet, 0 < code c ∧ code c < 32 := by decide +kernel

theorem newline_not_mem : '\n' ∉ alphabet := by decide

theorem decodeCode_code : ∀ c ∈ alphabet, decodeCode (code c) = some c := by decide +kernel

theorem decodeCode_zero : decodeCode 0 = none := by decide +kernel

theorem bitN_le_one (d i : Nat) : bitN d i = 0 ∨ bitN d i = 1 := by
  unfold bitN; omega

/-! ## Lines and their typesetting -/

theorem takeWhile_join (top bot : Text) (h : ∀ c ∈ top, c ≠ '\n') :
    (top ++ '\n' :: bot).takeWhile (· != '\n') = top := by
  induction top with
  | nil => simp
  | cons c r ih =>
    have hc : c ≠ '\n' := h c (by simp)
    simp [hc, ih (fun d hd => h d (by simp [hd]))]

theorem dropWhile_join (top bot : Text) (h : ∀ c ∈ top, c ≠ '\n') :
    (top ++ '\n' :: bot).dropWhile (· != '\n') = '\n' :: bot := by
  induction top with
  | nil => simp
  | cons c r ih =>
    have hc : c ≠ '\n' := h c (by simp)
    simp [hc, ih (fun d hd => h d (by simp [hd]))]

theorem splitLines_join (top bot : Text) (h : ∀ c ∈ top, c ≠ '\n') :
    splitLines (top ++ '\n' :: bot) = (top, bot) := by
  simp [splitLines, takeWhile_join top bot h, dropWhile_join top bot h]

theorem good_iff (s : Text) :
    good s = true ↔ s ≠ [] ∧ (∀ c ∈ s, c ∈ alphabet) ∧ s.length ≤ W := by
  simp [good, and_assoc]

theorem no_newline_of_good {s : Text} (h : good s = true) : ∀ c ∈ s, c ≠ '\n' := by
  intro c hc heq
  exact newline_not_mem (heq ▸ ((good_iff s).1 h).2.1 c hc)

theorem wf_join {top bot : Text} (ht : good top = true) (hb : good bot = true) :
    wf (top ++ '\n' :: bot) = true := by
  unfold wf
  rw [splitLines_join top bot (no_newline_of_good ht), ht, hb,
    decide_eq_true (rfl : top ++ '\n' :: bot = top ++ '\n' :: bot)]
  rfl

theorem wf_spec {t : Text} (h : wf t = true) :
    t = (splitLines t).1 ++ '\n' :: (splitLines t).2 ∧ good (splitLines t).1 = true ∧
      good (splitLines t).2 = true := by
  simp only [wf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.symm, h.1.2, h.2⟩

theorem typesetLines_cell (top bot : Text) {L p i : Nat} (hL : L ≤ 1) (hp : p < W) (hi : i < 24) :
    typesetLines top bot (4 * (W - 1 - p) + i % 4) (6 * L + i / 4) =
      (bitN (cellCode (if L = 1 then top else bot) p) i == 1) := by
  unfold W at hp
  have h1 : (4 * (W - 1 - p) + i % 4) / 4 = W - 1 - p := by unfold W; omega
  have h2 : (4 * (W - 1 - p) + i % 4) % 4 = i % 4 := by omega
  have h3 : (6 * L + i / 4) / 6 = L := by omega
  have h4 : (6 * L + i / 4) % 6 = i / 4 := by omega
  have h5 : W - 1 - (W - 1 - p) = p := by unfold W; omega
  have h6 : 4 * (i / 4) + i % 4 = i := by omega
  have h7 : W - 1 - p < W := by unfold W; omega
  simp [typesetLines, h1, h2, h3, h4, h5, h6, h7, hL]

theorem bits_beq {a b : Nat} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a == 1) = (b == 1) ↔ a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem decodeCell_typeset (top bot : Text) {L p : Nat} (hL : L ≤ 1) (hp : p < W) :
    decodeCell (typesetLines top bot) L p = decodeCode (cellCode (if L = 1 then top else bot) p) := by
  unfold decodeCell decodeCode
  congr 1
  funext c
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  have key := fun i => bits_beq (bitN_le_one (cellCode (if L = 1 then top else bot) p) i)
    (bitN_le_one (code c) i)
  constructor
  · intro h i hi
    have := h i hi
    rw [typesetLines_cell top bot hL hp hi] at this
    exact (key i).1 this
  · intro h i hi
    rw [typesetLines_cell top bot hL hp hi]
    exact (key i).2 (h i hi)

theorem decodeCode_cellCode {s : Text} (hs : ∀ c ∈ s, c ∈ alphabet) (p : Nat) :
    decodeCode (cellCode s p) = s.reverse[p]? := by
  unfold cellCode
  cases h : s.reverse[p]? with
  | none => simpa using decodeCode_zero
  | some c =>
    have hc : c ∈ s := List.mem_reverse.1 (List.mem_of_getElem? h)
    simpa using decodeCode_code c (hs c hc)

theorem filterMap_congr' {α β : Type} {f g : α → Option β} : ∀ (l : List α),
    (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (by simp),
      filterMap_congr' l (fun b hb => h b (by simp [hb]))]

theorem filterMap_range_reverse {α : Type} : ∀ (n : Nat) (l : List α), l.length ≤ n →
    (List.range n).reverse.filterMap (fun p => l.reverse[p]?) = l
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [this]
  | n + 1, l, h => by
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.filterMap_cons]
    by_cases hl : l.length = n + 1
    · cases l with
      | nil => exact absurd hl (by simp only [List.length_nil]; omega)
      | cons a tl =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        have hn : (a :: tl).reverse[n]? = some a := by
          simp [List.reverse_cons, hl]
        rw [hn]
        simp only [List.cons.injEq, true_and]
        rw [filterMap_congr' (g := fun p => tl.reverse[p]?)]
        · exact filterMap_range_reverse n tl (by omega)
        · intro p hp
          simp only [List.mem_reverse, List.mem_range] at hp
          simp [List.reverse_cons, List.getElem?_append_left, hl, hp]
    · have hn : l.reverse[n]? = none := by simp; omega
      rw [hn]
      exact filterMap_range_reverse n l (by omega)

theorem decodeLine_typeset {top bot : Text} (ht : good top = true) (hb : good bot = true)
    {L : Nat} (hL : L ≤ 1) :
    decodeLine (typesetLines top bot) L = if L = 1 then top else bot := by
  have hs : good (if L = 1 then top else bot) = true := by split <;> assumption
  obtain ⟨-, hmem, hlen⟩ := (good_iff _).1 hs
  unfold decodeLine
  rw [filterMap_congr' (g := fun p => (if L = 1 then top else bot).reverse[p]?)]
  · exact filterMap_range_reverse W _ hlen
  · intro p hp
    simp only [List.mem_reverse, List.mem_range] at hp
    rw [decodeCell_typeset top bot hL hp, decodeCode_cellCode hmem]

theorem decode_typeset {t : Text} (h : wf t = true) : decode (typeset t) = t := by
  obtain ⟨ht, h1, h2⟩ := wf_spec h
  unfold decode typeset
  rw [decodeLine_typeset h1 h2 (by decide), decodeLine_typeset h1 h2 (by decide)]
  simp only [if_true, show ¬((0 : Nat) = 1) from by decide, if_false]
  exact ht.symm

/-! ## Numerals -/

/-- Base-32 value of a list of digits, least significant first. -/
def numN : List Nat → Nat
  | [] => 0
  | d :: r => d + 32 * numN r

/-- A line read as a base-32 numeral, most significant digit first, with the characters' codes
as digits. -/
def num (x : Text) : Nat := numN (x.reverse.map code)

theorem numN_digit : ∀ (l : List Nat), (∀ d ∈ l, d < 32) → ∀ p, numN l / 32 ^ p % 32 = (l[p]?).getD 0
  | [], _, p => by simp [numN]
  | d :: r, h, p => by
    have hd : d < 32 := h d (by simp)
    cases p with
    | zero => simp [numN]; omega
    | succ p =>
      rw [numN, Nat.pow_succ', ← Nat.div_div_eq_div_mul,
        show (d + 32 * numN r) / 32 = numN r by omega]
      simpa using numN_digit r (fun e he => h e (by simp [he])) p

theorem num_digit {x : Text} (hx : ∀ c ∈ x, c ∈ alphabet) (p : Nat) :
    num x / 32 ^ p % 32 = cellCode x p := by
  have hl : ∀ d ∈ x.reverse.map code, d < 32 := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    exact (code_bounds c (hx c (List.mem_reverse.1 hc))).2
  unfold num cellCode
  rw [numN_digit _ hl p, List.getElem?_map]

theorem num_pos {x : Text} (hx : good x = true) : 0 < num x := by
  obtain ⟨hne, hmem, -⟩ := (good_iff x).1 hx
  have h0 := num_digit hmem 0
  unfold cellCode at h0
  cases h : x.reverse with
  | nil => simp_all
  | cons c r =>
    have hc : c ∈ alphabet := hmem c (List.mem_reverse.1 (by simp [h]))
    rw [h] at h0
    have := (code_bounds c hc).1
    simp at h0
    omega

def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

theorem digitChar_facts : ∀ d : Fin 10, code (digitChar d) = d + 1 ∧ digitChar d ∈ alphabet ∧
    (digitChar d).isDigit = true ∧ (digitChar d).toNat - 48 = d := by decide

/-- Decimal digits, least significant first, with `f` steps of fuel. -/
def decF : Nat → Nat → Text
  | 0, _ => []
  | f + 1, n => if n < 10 then [digitChar n] else digitChar (n % 10) :: decF f (n / 10)

def decR (n : Nat) : Text := decF (n + 1) n

/-- The decimal numeral of `n`. -/
def dec (n : Nat) : Text := (decR n).reverse

theorem decF_get : ∀ (f n p : Nat), n < f → 0 < n →
    (decF f n)[p]? = if 0 < n / 10 ^ p then some (digitChar (n / 10 ^ p % 10)) else none
  | 0, _, _, h, _ => by omega
  | f + 1, n, p, h, hn => by
    unfold decF
    by_cases h10 : n < 10
    · rw [if_pos h10]
      cases p with
      | zero => simp [Nat.mod_eq_of_lt h10, hn]
      | succ p =>
        have : n / 10 ^ (p + 1) = 0 :=
          Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h10 (by
            calc 10 = 10 ^ 1 := rfl
              _ ≤ 10 ^ (p + 1) := Nat.pow_le_pow_right (by decide) (by omega)))
        rw [this, if_neg (Nat.lt_irrefl 0)]
        rfl
    · rw [if_neg h10]
      cases p with
      | zero => simp; omega
      | succ p =>
        rw [List.getElem?_cons_succ, decF_get f (n / 10) p (by omega) (by omega), Nat.pow_succ,
          Nat.mul_comm, ← Nat.div_div_eq_div_mul]

theorem decR_get {n : Nat} (hn : 0 < n) (p : Nat) :
    (decR n)[p]? = if 0 < n / 10 ^ p then some (digitChar (n / 10 ^ p % 10)) else none :=
  decF_get (n + 1) n p (by omega) hn

theorem cellCode_dec {n : Nat} (hn : 0 < n) (p : Nat) :
    cellCode (dec n) p = if 0 < n / 10 ^ p then n / 10 ^ p % 10 + 1 else 0 := by
  unfold cellCode dec
  rw [List.reverse_reverse, decR_get hn]
  split
  · have := (digitChar_facts ⟨n / 10 ^ p % 10, Nat.mod_lt _ (by decide)⟩).1
    simpa using this
  · rfl

theorem decF_mem : ∀ (f n : Nat), ∀ c ∈ decF f n, ∃ d : Fin 10, c = digitChar d
  | 0, _, c, h => by simp [decF] at h
  | f + 1, n, c, h => by
    unfold decF at h
    split at h
    · simp only [List.mem_singleton] at h
      exact ⟨⟨n, by omega⟩, h⟩
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact ⟨⟨n % 10, Nat.mod_lt _ (by decide)⟩, h⟩
      · exact decF_mem f (n / 10) c h

theorem dec_mem {n : Nat} : ∀ c ∈ dec n, ∃ d : Fin 10, c = digitChar d := by
  intro c hc
  exact decF_mem _ _ c (List.mem_reverse.1 hc)

theorem dec_ne_nil (n : Nat) : dec n ≠ [] := by
  unfold dec decR decF
  split <;> simp

/-- Read a decimal numeral. -/
def parseDec (s : Text) : Nat := s.foldl (fun a c => 10 * a + (c.toNat - 48)) 0

theorem decF_val : ∀ (f n : Nat), n < f →
    (decF f n).foldr (fun c a => 10 * a + (c.toNat - 48)) 0 = n
  | 0, _, h => by omega
  | f + 1, n, h => by
    unfold decF
    split
    · rename_i h10
      have := (digitChar_facts ⟨n, h10⟩).2.2.2
      simp [this]
    · have := (digitChar_facts ⟨n % 10, Nat.mod_lt _ (by decide)⟩).2.2.2
      simp only [List.foldr_cons, decF_val f (n / 10) (by omega), this]
      omega

theorem parseDec_dec (n : Nat) : parseDec (dec n) = n := by
  unfold parseDec dec
  rw [List.foldl_reverse]
  exact decF_val _ _ (by omega)

/-! ## Interleaving two lines into one numeral -/

def inter : List Nat → List Nat → List Nat
  | [], [] => []
  | a :: as, [] => a :: 0 :: inter as []
  | [], b :: bs => 0 :: b :: inter [] bs
  | a :: as, b :: bs => a :: b :: inter as bs

theorem inter_get : ∀ (as bs : List Nat) (p : Nat),
    ((inter as bs)[2 * p]?).getD 0 = (as[p]?).getD 0 ∧
      ((inter as bs)[2 * p + 1]?).getD 0 = (bs[p]?).getD 0
  | [], [], _ => by simp [inter]
  | a :: as, [], p => by
    cases p with
    | zero => simp [inter]
    | succ p =>
      have := inter_get as [] p
      simp only [inter, show 2 * (p + 1) = 2 * p + 1 + 1 by omega, List.getElem?_cons_succ]
      simpa using this
  | [], b :: bs, p => by
    cases p with
    | zero => simp [inter]
    | succ p =>
      have := inter_get [] bs p
      simp only [inter, show 2 * (p + 1) = 2 * p + 1 + 1 by omega, List.getElem?_cons_succ]
      simpa using this
  | a :: as, b :: bs, p => by
    cases p with
    | zero => simp [inter]
    | succ p =>
      have := inter_get as bs p
      simp only [inter, show 2 * (p + 1) = 2 * p + 1 + 1 by omega, List.getElem?_cons_succ]
      simpa using this

theorem inter_lt : ∀ (as bs : List Nat), (∀ d ∈ as, d < 32) → (∀ d ∈ bs, d < 32) →
    ∀ d ∈ inter as bs, d < 32
  | [], [], _, _ => by simp [inter]
  | a :: as, [], ha, hb => by
    intro d hd
    simp only [inter, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact ha _ (by simp)
    · decide
    · exact inter_lt as [] (fun e he => ha e (by simp [he])) hb d hd
  | [], b :: bs, ha, hb => by
    intro d hd
    simp only [inter, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · decide
    · exact hb _ (by simp)
    · exact inter_lt [] bs ha (fun e he => hb e (by simp [he])) d hd
  | a :: as, b :: bs, ha, hb => by
    intro d hd
    simp only [inter, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact ha _ (by simp)
    · exact hb _ (by simp)
    · exact inter_lt as bs (fun e he => ha e (by simp [he])) (fun e he => hb e (by simp [he])) d hd

theorem cellCode_eq (s : Text) (p : Nat) : cellCode s p = ((s.reverse.map code)[p]?).getD 0 := by
  unfold cellCode
  rw [List.getElem?_map]

/-! ## Terms -/

inductive Term
  | num (n : Nat)
  | x
  | y
  | k
  | add (a b : Term)
  | sub (a b : Term)
  | mul (a b : Term)
  | div (a b : Term)
  | mod (a b : Term)
  | pow (a b : Term)
  deriving DecidableEq

/-- Natural-number semantics: `-` truncates and `/` rounds down. -/
def Term.eval (X Y K : Nat) : Term → Nat
  | num n => n
  | x => X
  | y => Y
  | k => K
  | add a b => a.eval X Y K + b.eval X Y K
  | sub a b => a.eval X Y K - b.eval X Y K
  | mul a b => a.eval X Y K * b.eval X Y K
  | div a b => a.eval X Y K / b.eval X Y K
  | mod a b => a.eval X Y K % b.eval X Y K
  | pow a b => a.eval X Y K ^ b.eval X Y K

def readNum (acc : Nat) : Text → Nat × Text
  | c :: r => if c.isDigit then readNum (10 * acc + (c.toNat - 48)) r else (acc, c :: r)
  | [] => (acc, [])

/-! A recursive-descent parser with fuel: `^` binds tightest (and does not chain), then
`* / %`, then `+ -`, all left-associative. -/

mutual
def pSum : Nat → Text → Option (Term × Text)
  | 0, _ => none
  | n + 1, s =>
    match pProd n s with
    | some (a, r) => pSumLoop n a r
    | none => none

def pSumLoop : Nat → Term → Text → Option (Term × Text)
  | 0, _, _ => none
  | _ + 1, a, [] => some (a, [])
  | n + 1, a, c :: r =>
    if c = '+' then
      match pProd n r with
      | some (b, r') => pSumLoop n (.add a b) r'
      | none => none
    else if c = '-' then
      match pProd n r with
      | some (b, r') => pSumLoop n (.sub a b) r'
      | none => none
    else some (a, c :: r)

def pProd : Nat → Text → Option (Term × Text)
  | 0, _ => none
  | n + 1, s =>
    match pPow n s with
    | some (a, r) => pProdLoop n a r
    | none => none

def pProdLoop : Nat → Term → Text → Option (Term × Text)
  | 0, _, _ => none
  | _ + 1, a, [] => some (a, [])
  | n + 1, a, c :: r =>
    if c = '*' then
      match pPow n r with
      | some (b, r') => pProdLoop n (.mul a b) r'
      | none => none
    else if c = '/' then
      match pPow n r with
      | some (b, r') => pProdLoop n (.div a b) r'
      | none => none
    else if c = '%' then
      match pPow n r with
      | some (b, r') => pProdLoop n (.mod a b) r'
      | none => none
    else some (a, c :: r)

def pPow : Nat → Text → Option (Term × Text)
  | 0, _ => none
  | n + 1, s =>
    match pAtom n s with
    | some (a, c :: r) =>
      if c = '^' then
        match pAtom n r with
        | some (b, r') => some (.pow a b, r')
        | none => none
      else some (a, c :: r)
    | some (a, []) => some (a, [])
    | none => none

def pAtom : Nat → Text → Option (Term × Text)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, c :: r =>
    if c = '(' then
      match pSum n r with
      | some (a, d :: r') => if d = ')' then some (a, r') else none
      | _ => none
    else if c = 'x' then some (.x, r)
    else if c = 'y' then some (.y, r)
    else if c = 'k' then some (.k, r)
    else if c.isDigit then some (.num (readNum 0 (c :: r)).1, (readNum 0 (c :: r)).2)
    else none
end

def stripPrefix : Text → Text → Option Text
  | [], s => some s
  | c :: p, d :: s => if c = d then stripPrefix p s else none
  | _ :: _, [] => none

/-- Parse a first line of the form `0<E,k=` into `E`. -/
def parseBody (top : Text) : Option Term :=
  match stripPrefix "0<".toList top with
  | some r =>
    match stripPrefix ",k=".toList.reverse r.reverse with
    | some b =>
      match pSum (8 * b.length + 8) b.reverse with
      | some (t, []) => some t
      | _ => none
    | none => none
  | none => none

/-- Parse a formula: the first line `0<E,k=`, then a line of decimal digits. -/
def parseFormula (f : Text) : Option (Term × Nat) :=
  if decide ((splitLines f).1 ++ '\n' :: (splitLines f).2 = f) && !(splitLines f).2.isEmpty &&
      (splitLines f).2.all Char.isDigit then
    (parseBody (splitLines f).1).map fun t => (t, parseDec (splitLines f).2)
  else none

/-- The points `(X, Y)` with `0 < E(X, Y, K)`. -/
def plot (t : Term) (K : Nat) : Pic := fun X Y => decide (0 < t.eval X Y K)

theorem dec_digits (n : Nat) : (dec n).all Char.isDigit = true := by
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨d, rfl⟩ := dec_mem c hc
  exact (digitChar_facts d).2.2.1

theorem parseFormula_join (c : Text) (n : Nat) (hc : ∀ ch ∈ c, ch ≠ '\n') :
    parseFormula (c ++ '\n' :: dec n) = (parseBody c).map fun t => (t, n) := by
  unfold parseFormula
  rw [splitLines_join c (dec n) hc, parseDec_dec, dec_digits,
    decide_eq_true (rfl : c ++ '\n' :: dec n = c ++ '\n' :: dec n)]
  have h : (!(dec n).isEmpty) = true := by
    cases h : dec n with
    | nil => exact absurd h (dec_ne_nil n)
    | cons a r => rfl
  rw [h]
  rfl

/-! ## The template and the quotation -/

/-- The first line of the template. Its cell `p` (from the right) on the top line is digit `p` of
`k` in base 32; on the bottom line it is decimal digit `p` of `k`, or blank. -/
def tmplText : Text :=
  "0<(".toList ++ dec F ++ "/2^(24*(y/6*(k/32^(".toList ++ dec W ++
    "-1-x/4)%32)+(1-y/6)*((k/10^(".toList ++ dec W ++ "-1-x/4)%10+1)*(1-1/(k/10^(".toList ++
    dec W ++ "-1-x/4)+1))))+4*(y%6)+x%4))%2*(2/(y/6+1))*(".toList ++ dec W ++
    "/(x/4+1)),k=".toList

/-- The first line of a quotation. Here `k` interleaves the two lines: base-32 digit `2p + L` is
cell `p` of line `L`. -/
def e2Text : Text :=
  "0<(".toList ++ dec F ++ "/2^(24*(k/32^(2*(".toList ++ dec W ++
    "-1-x/4)+y/6)%32)+4*(y%6)+x%4))%2*(2/(y/6+1))*(".toList ++ dec W ++ "/(x/4+1)),k=".toList

def pW : Term := .sub (.sub (.num W) (.num 1)) (.div .x (.num 4))

def lT : Term := .div .y (.num 6)

def qT : Term := .div .k (.pow (.num 10) pW)

def dT : Term :=
  .add (.mul lT (.mod (.div .k (.pow (.num 32) pW)) (.num 32)))
    (.mul (.sub (.num 1) lT) (.mul (.add (.mod qT (.num 10)) (.num 1))
      (.sub (.num 1) (.div (.num 1) (.add qT (.num 1))))))

/-- `(F/2^(24*d+4*(y%6)+x%4))%2*(2/(y/6+1))*(W/(x/4+1))`: the pixel of the glyph with code `d`,
cut off above line 1 and to the right of column `W`. -/
def frame (d : Term) : Term :=
  .mul (.mul (.mod (.div (.num F) (.pow (.num 2)
    (.add (.add (.mul (.num 24) d) (.mul (.num 4) (.mod .y (.num 6)))) (.mod .x (.num 4)))))
    (.num 2)) (.div (.num 2) (.add lT (.num 1)))) (.div (.num W) (.add (.div .x (.num 4)) (.num 1)))

def tmplTerm : Term := frame dT

def e2Term : Term := frame (.mod (.div .k (.pow (.num 32) (.add (.mul (.num 2) pW) lT))) (.num 32))

theorem parseBody_tmpl : parseBody tmplText = some tmplTerm := by decide +kernel

theorem parseBody_e2 : parseBody e2Text = some e2Term := by decide +kernel

theorem tmplText_no_newline : ∀ c ∈ tmplText, c ≠ '\n' := by decide +kernel

theorem e2Text_no_newline : ∀ c ∈ e2Text, c ≠ '\n' := by decide +kernel

/-- `sub c x` is the formula with first line `c` and constant `k` = `x` read in base 32. -/
def sub (c x : Text) : Text := c ++ '\n' :: dec (num x)

def kq (t : Text) : Nat :=
  numN (inter ((splitLines t).2.reverse.map code) ((splitLines t).1.reverse.map code))

/-- A formula that plots the text `t`. -/
def quote (t : Text) : Text := e2Text ++ '\n' :: dec (kq t)

theorem parseFormula_sub (x : Text) : parseFormula (sub tmplText x) = some (tmplTerm, num x) := by
  rw [sub, parseFormula_join _ _ tmplText_no_newline, parseBody_tmpl]
  rfl

theorem parseFormula_quote (t : Text) : parseFormula (quote t) = some (e2Term, kq t) := by
  rw [quote, parseFormula_join _ _ e2Text_no_newline, parseBody_e2]
  rfl

/-! ## The formulas plot what they should -/

theorem eval_frame (d : Term) (X Y K : Nat) :
    (frame d).eval X Y K =
      bitN (d.eval X Y K) (4 * (Y % 6) + X % 4) * (2 / (Y / 6 + 1)) * (W / (X / 4 + 1)) := by
  simp only [frame, lT, Term.eval, bitN, Nat.add_assoc]

theorem frame_pos (b L X : Nat) (hb : b ≤ 1) :
    0 < b * (2 / (L + 1)) * (W / (X / 4 + 1)) ↔ L ≤ 1 ∧ X / 4 < W ∧ b = 1 := by
  have h1 : 0 < 2 / (L + 1) ↔ L ≤ 1 := by
    rw [Nat.div_pos_iff]; exact ⟨fun h => by omega, fun h => ⟨by omega, by omega⟩⟩
  have h2 : 0 < W / (X / 4 + 1) ↔ X / 4 < W := by
    rw [Nat.div_pos_iff]; exact ⟨fun h => by omega, fun h => ⟨by omega, by omega⟩⟩
  rw [Nat.pos_iff_ne_zero, Nat.mul_ne_zero_iff, Nat.mul_ne_zero_iff, ← Nat.pos_iff_ne_zero,
    ← Nat.pos_iff_ne_zero, ← Nat.pos_iff_ne_zero, h1, h2]
  exact ⟨fun ⟨⟨_, hL⟩, hX⟩ => ⟨hL, hX, by omega⟩, fun ⟨hL, hX, _⟩ => ⟨⟨by omega, hL⟩, hX⟩⟩

/-- If the code in the right cell is right, the formula plots the typesetting. -/
theorem plot_frame (d : Term) (K : Nat) (top bot : Text)
    (hd : ∀ X Y, Y / 6 ≤ 1 →
      d.eval X Y K = cellCode (if Y / 6 = 1 then top else bot) (W - 1 - X / 4)) :
    plot (frame d) K = typesetLines top bot := by
  funext X Y
  apply Bool.eq_iff_iff.2
  have hb : bitN (d.eval X Y K) (4 * (Y % 6) + X % 4) ≤ 1 := by
    rcases bitN_le_one (d.eval X Y K) (4 * (Y % 6) + X % 4) with h | h <;> omega
  simp only [plot, decide_eq_true_eq, eval_frame, frame_pos _ _ _ hb, typesetLines,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hL, hX, h⟩
    exact ⟨⟨hL, hX⟩, by rwa [← hd X Y hL]⟩
  · rintro ⟨⟨hL, hX⟩, h⟩
    exact ⟨hL, hX, by rwa [hd X Y hL]⟩

/-- The side condition on substitution arguments: both lines of `sub x x` can be typeset. -/
def okB (x : Text) : Bool := good x && good (dec (num x))

theorem wf_sub {x : Text} (hx : okB x = true) : wf (sub x x) = true := by
  simp only [okB, Bool.and_eq_true] at hx
  exact wf_join hx.1 hx.2

theorem plot_tmpl {x : Text} (hx : okB x = true) : plot tmplTerm (num x) = typeset (sub x x) := by
  simp only [okB, Bool.and_eq_true] at hx
  obtain ⟨-, hmem, -⟩ := (good_iff x).1 hx.1
  have hK := num_pos hx.1
  rw [typeset, sub, splitLines_join x _ (no_newline_of_good hx.1)]
  apply plot_frame
  intro X Y hL
  simp only [dT, lT, pW, qT, Term.eval]
  rcases (by omega : Y / 6 = 0 ∨ Y / 6 = 1) with h | h
  · rw [h, if_neg (by decide), cellCode_dec hK]
    generalize num x / 10 ^ (W - 1 - X / 4) = q
    rcases Nat.eq_zero_or_pos q with hq | hq
    · simp [hq]
    · simp [hq, Nat.div_eq_of_lt (by omega : 1 < q + 1)]
  · rw [h, num_digit hmem]
    simp

theorem plot_e2 {t : Text} (ht : wf t = true) : plot e2Term (kq t) = typeset t := by
  obtain ⟨-, h1, h2⟩ := wf_spec ht
  have hlt (s : Text) (hs : good s = true) : ∀ d ∈ s.reverse.map code, d < 32 := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    exact (code_bounds c (((good_iff s).1 hs).2.1 c (List.mem_reverse.1 hc))).2
  apply plot_frame
  intro X Y hL
  simp only [pW, lT, Term.eval, kq]
  rw [numN_digit _ (inter_lt _ _ (hlt _ h2) (hlt _ h1))]
  have hi := inter_get ((splitLines t).2.reverse.map code) ((splitLines t).1.reverse.map code)
    (W - 1 - X / 4)
  rcases (by omega : Y / 6 = 0 ∨ Y / 6 = 1) with h | h
  · rw [h, Nat.add_zero, hi.1, cellCode_eq]
    simp
  · rw [h, hi.2, cellCode_eq]
    simp

/-! ## The representation system and the engine -/

def render (t : Text) : Pic ⊕ Text := if wf t then .inl (typeset t) else .inr t

def scan : Pic ⊕ Text → Option Text
  | .inl p => some (decode p)
  | .inr t => some t

def system : System Text (Pic ⊕ Text) where
  disp f p := ∃ t K, parseFormula f = some (t, K) ∧ p = .inl (plot t K)
  scan := scan
  render := render
  scan_render t := by
    unfold render
    split
    · simp [scan, decode_typeset ‹_›]
    · rfl

def quotation : Quotation system where
  Dom t := wf t = true
  q := quote
  disp_q t ht := ⟨.inl (typeset t), ⟨e2Term, kq t, parseFormula_quote t, by rw [plot_e2 ht]⟩,
    by simp [system, render, ht]⟩

def diagonal : Diagonal system quotation where
  sub := sub
  a := tmplText
  Ok x := okB x = true
  spec := by
    intro x hx s ⟨p, ⟨t, K, hf, hp⟩, hs⟩
    change parseFormula (quote (sub x x)) = _ at hf
    rw [parseFormula_quote] at hf
    cases hf
    rw [plot_e2 (wf_sub hx)] at hp
    subst hp
    change some (decode (typeset (sub x x))) = some s at hs
    rw [decode_typeset (wf_sub hx), Option.some.injEq] at hs
    subst hs
    refine ⟨.inl (plot tmplTerm (num x)), ⟨tmplTerm, num x, parseFormula_sub x, rfl⟩, ?_⟩
    change some (decode (plot tmplTerm (num x))) = _
    rw [plot_tmpl hx, decode_typeset (wf_sub hx)]

/-- The engine's output: a two-line formula whose plot is its own text. -/
def quine : Text := diagonal.quine

theorem ok_tmpl : okB tmplText = true := by decide +kernel

theorem quine_correct : system.IsQuine quine :=
  diagonal.isQuine ok_tmpl (wf_sub ok_tmpl)

/-- The plot of a formula, if it parses (for drawing it). -/
def formulaPlot (f : Text) : Option Pic := (parseFormula f).map fun (t, K) => plot t K

end QuineEngine.SelfPlottingFormula
