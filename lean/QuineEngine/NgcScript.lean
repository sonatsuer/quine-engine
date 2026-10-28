import QuineEngine.PsScript

/-!
# G-code files that store their own text as numbers: the model

RS274NGC (LinuxCNC G-code) has no strings, so the G-code quines are data + code files:
```
#1001=19230712283015
#1002=...
...
#nnnn=00000000000000
c
```
The data block stores a text in the parameters #1001, #1002, …, up to a zero: each holds seven
two-digit codes, where the code of a character is one more than its position in the alphabet `A`,
and `00` is padding. The code `c` must be `pre` followed by `O100CALL[m]`, a newline and `M2`,
where `pre` is a quine-specific library and the mode `m` is 0 or 1: mode 0 shows the stored text,
mode 1 shows the data block of the stored text followed by the stored text.

The data block occupies at most #1001–#1999, so that it stays clear of the library's parameters
and of LinuxCNC's system parameters. The semantics is deliberately conservative: files of any
other shape display nothing.
-/

namespace QuineEngine.NgcScript

open QuineEngine.PsScript (stripPrefix stripPrefix_append)

abbrev Text := List Char

/-! ## Digits -/

def digit (n : Nat) : Char := Char.ofNat (48 + n)

def digitVal (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48) else none

theorem digitVal_digit (n : Nat) (h : n < 10) : digitVal (digit n) = some n := by
  have key : ∀ k : Fin 10, digitVal (digit k) = some k := by decide
  exact key ⟨n, h⟩

/-- Two decimal digits. -/
def dig2 (n : Nat) : Text := [digit (n / 10), digit (n % 10)]

/-- The last four decimal digits. -/
def dig4 (n : Nat) : Text :=
  [digit (n / 1000 % 10), digit (n / 100 % 10), digit (n / 10 % 10), digit (n % 10)]

/-- Read `k` two-digit numbers. -/
def readPairs : Nat → Text → Option (List Nat × Text)
  | 0, r => some ([], r)
  | k + 1, a :: b :: r =>
    match digitVal a, digitVal b with
    | some x, some y => (readPairs k r).map fun (cs, r') => ((10 * x + y) :: cs, r')
    | _, _ => none
  | _ + 1, _ => none

theorem readPairs_dig2 (r : Text) : ∀ l : List Nat, l.all (· < 100) = true →
    readPairs l.length (l.flatMap dig2 ++ r) = some (l, r) := by
  intro l hl
  induction l with
  | nil => rfl
  | cons n l ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
    have h1 : n / 10 < 10 := by omega
    have h2 : n % 10 < 10 := Nat.mod_lt _ (by decide)
    have hn : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
    simp only [List.length_cons, List.flatMap_cons, dig2, List.cons_append, List.nil_append,
      readPairs, digitVal_digit _ h1, digitVal_digit _ h2, ih hl.2, hn]
    rfl

/-! ## The data block -/

/-- Seven codes, padded with zeros. -/
def pad7 (cs : List Nat) : List Nat := cs ++ List.replicate (7 - cs.length) 0

/-- The line `#i=` followed by seven two-digit codes. -/
def lineOf (i : Nat) (cs : List Nat) : Text :=
  '#' :: (dig4 i ++ ('=' :: ((pad7 cs).flatMap dig2 ++ ['\n'])))

/-- The lines for the codes `cs` from parameter `i`, then a zero line; `k` bounds the lines. -/
def blocks : Nat → Nat → List Nat → Text
  | 0, i, _ => lineOf i []
  | _ + 1, i, [] => lineOf i []
  | k + 1, i, c :: cs => lineOf i ((c :: cs).take 7) ++ blocks k (i + 1) ((c :: cs).drop 7)

variable (A : List Char)

/-- The code of a character: one more than its position in the alphabet. -/
def code (c : Char) : Nat := A.idxOf c + 1

def inA (c : Char) : Bool := decide (c ∈ A)

/-- The data block of a text. -/
def dataBlock (x : Text) : Text := blocks x.length 1001 (x.map (code A))

/-- Read data lines from parameter `i`, up to a zero line; `k` bounds the lines. -/
def parseData : Nat → Nat → Text → Option (List Nat × Text)
  | 0, _, _ => none
  | k + 1, i, r =>
    if i ≤ 1999 then
      match stripPrefix ('#' :: (dig4 i ++ ['='])) r with
      | some r =>
        match readPairs 7 r with
        | some (cs, '\n' :: r') =>
          if cs.all (· == 0) then some ([], r')
          else (parseData k (i + 1) r').map fun (ds, r'') => (cs.filter (· != 0) ++ ds, r'')
        | _ => none
      | none => none
    else none

/-- The characters with the given codes. -/
def decodeCodes : List Nat → Option Text
  | [] => some []
  | n :: ns => (A[n - 1]?).bind fun c => (decodeCodes ns).map (c :: ·)

/-- Parse a file into the stored text and the code. -/
def parseFile (f : Text) : Option (Text × Text) :=
  match parseData (f.length + 1) 1001 f with
  | some (cs, c) => (decodeCodes A cs).map (·, c)
  | none => none

/-! ## Correctness of the data block -/

theorem pad7_length (cs : List Nat) (h : cs.length ≤ 7) : (pad7 cs).length = 7 := by
  simp only [pad7, List.length_append, List.length_replicate]
  omega

theorem stripPrefix_lineOf (i : Nat) (cs : List Nat) (c : Text) :
    stripPrefix ('#' :: (dig4 i ++ ['='])) (lineOf i cs ++ c) =
      some ((pad7 cs).flatMap dig2 ++ ('\n' :: c)) := by
  have : lineOf i cs ++ c =
      ('#' :: (dig4 i ++ ['='])) ++ ((pad7 cs).flatMap dig2 ++ ('\n' :: c)) := by
    simp [lineOf]
  rw [this, stripPrefix_append]

theorem readPairs_pad7 (cs : List Nat) (hl : cs.length ≤ 7) (h : cs.all (· < 100) = true)
    (c : Text) :
    readPairs 7 ((pad7 cs).flatMap dig2 ++ ('\n' :: c)) = some (pad7 cs, '\n' :: c) := by
  have hp : (pad7 cs).all (· < 100) = true := by
    simp only [pad7, List.all_append, h, Bool.true_and, List.all_eq_true, List.mem_replicate,
      decide_eq_true_eq]
    intro x hx
    rw [hx.2]
    decide
  have := readPairs_dig2 ('\n' :: c) (pad7 cs) hp
  rwa [pad7_length cs hl] at this

theorem filter_pad7 (cs : List Nat) (h : cs.all (· != 0) = true) :
    (pad7 cs).filter (· != 0) = cs := by
  simp only [pad7, List.filter_append]
  rw [List.filter_eq_self.2 (by simpa using h)]
  have : (List.replicate (7 - cs.length) 0).filter (· != 0) = [] := by
    induction 7 - cs.length with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  rw [this, List.append_nil]

theorem parseData_zero (n i : Nat) (hn : 1 ≤ n) (hi : i ≤ 1999) (c : Text) :
    parseData n i (lineOf i [] ++ c) = some ([], c) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [parseData, if_pos hi, stripPrefix_lineOf]
  dsimp only
  rw [readPairs_pad7 [] (by decide) rfl]
  rfl

theorem parseData_blocks (c : Text) : ∀ (k i : Nat) (cs : List Nat) (n : Nat),
    cs.length ≤ 7 * k → k + 1 ≤ n → i + k ≤ 1999 →
    cs.all (fun d => 0 < d && d < 100) = true →
    parseData n i (blocks k i cs ++ c) = some (cs, c) := by
  intro k
  induction k with
  | zero =>
    intro i cs n hl hn hi _
    have : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact parseData_zero n i hn (by omega) c
  | succ k ih =>
    intro i cs n hl hn hi hc
    cases cs with
    | nil => exact parseData_zero n i (by omega) (by omega) c
    | cons d ds =>
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hall : ∀ x ∈ d :: ds, 0 < x ∧ x < 100 := by
        simpa only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] using hc
      have htake : ((d :: ds).take 7).all (· < 100) = true := by
        simp only [List.all_eq_true, decide_eq_true_eq]
        exact fun x hx => (hall x (List.mem_of_mem_take hx)).2
      have hnz : ((d :: ds).take 7).all (· != 0) = true := by
        simp only [List.all_eq_true, bne_iff_ne, ne_eq]
        exact fun x hx => Nat.pos_iff_ne_zero.1 (hall x (List.mem_of_mem_take hx)).1
      have hdrop : ((d :: ds).drop 7).all (fun d => 0 < d && d < 100) = true := by
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact fun x hx => hall x (List.mem_of_mem_drop hx)
      have hlt : ((d :: ds).take 7).length ≤ 7 := List.length_take_le _ _
      have hrest := ih (i + 1) ((d :: ds).drop 7) n
        (by simp only [List.length_drop, List.length_cons] at hl ⊢; omega) (by omega) (by omega)
        hdrop
      rw [blocks, List.append_assoc, parseData, if_pos (by omega), stripPrefix_lineOf]
      dsimp only
      rw [readPairs_pad7 _ hlt htake]
      have hne : (pad7 ((d :: ds).take 7)).all (· == 0) = false := by
        simp only [pad7, List.take_succ_cons, List.cons_append, List.all_cons]
        have hd : d ≠ 0 := Nat.pos_iff_ne_zero.1 (hall d (List.mem_cons_self ..)).1
        have : (d == 0) = false := by
          cases d with
          | zero => exact absurd rfl hd
          | succ n => rfl
        rw [this, Bool.false_and]
      simp only [hne, hrest, Bool.false_eq_true, ↓reduceIte, Option.map_some, filter_pad7 _ hnz,
        List.take_append_drop]

/-- What the alphabet must satisfy: each character's code finds it, and fits two digits. -/
structure Alphabet : Prop where
  find : ∀ c ∈ A, A[code A c - 1]? = some c
  small : ∀ c ∈ A, code A c < 100

theorem decodeCodes_map (hA : Alphabet A) : ∀ x : Text, x.all (inA A) = true →
    decodeCodes A (x.map (code A)) = some x
  | [], _ => rfl
  | c :: x, h => by
    simp only [List.all_cons, Bool.and_eq_true, inA, decide_eq_true_eq] at h
    simp only [List.map_cons, decodeCodes, hA.find c h.1, Option.bind_some,
      decodeCodes_map hA x h.2, Option.map_some]

/-- The longest text a data block holds: 998 lines of seven characters. -/
def MAXLEN : Nat := 7 * 998

theorem blocks_fuel : ∀ k' k i (cs : List Nat), k ≤ k' → cs.length ≤ 7 * k →
    blocks k' i cs = blocks k i cs := by
  intro k'
  induction k' with
  | zero =>
    intro k i cs hk _
    have : k = 0 := by omega
    subst this
    rfl
  | succ k' ih =>
    intro k i cs hk hcs
    cases k with
    | zero =>
      have : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rfl
    | succ k =>
      cases cs with
      | nil => rfl
      | cons d ds =>
        simp only [blocks]
        rw [ih k (i + 1) _ (by omega)
          (by simp only [List.length_drop, List.length_cons] at hcs ⊢; omega)]

theorem length_le_blocks : ∀ k i (cs : List Nat), cs.length ≤ 7 * k →
    cs.length ≤ (blocks k i cs).length := by
  intro k
  induction k with
  | zero =>
    intro i cs hcs
    have : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact Nat.zero_le _
  | succ k ih =>
    intro i cs hcs
    cases cs with
    | nil => exact Nat.zero_le _
    | cons d ds =>
      have h1 := ih (i + 1) ((d :: ds).drop 7)
        (by simp only [List.length_drop, List.length_cons] at hcs ⊢; omega)
      have h2 : (lineOf i ((d :: ds).take 7)).length ≥ 7 := by
        simp only [lineOf, List.length_cons, List.length_append, dig4, List.length_flatMap, dig2]
        omega
      simp only [blocks, List.length_append]
      simp only [List.length_drop] at h1
      omega

theorem parseFile_dataBlock (hA : Alphabet A) {x : Text} (hx : x.all (inA A) = true)
    (hl : x.length ≤ MAXLEN) (c : Text) : parseFile A (dataBlock A x ++ c) = some (x, c) := by
  have hcodes : (x.map (code A)).all (fun d => 0 < d && d < 100) = true := by
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, Bool.and_eq_true,
      decide_eq_true_eq]
    intro d hd
    simp only [List.all_eq_true, inA, decide_eq_true_eq] at hx
    exact ⟨Nat.succ_pos _, hA.small d (hx d hd)⟩
  have hk1 : x.length ≤ 7 * ((x.length + 6) / 7) := by omega
  have hk2 : (x.length + 6) / 7 ≤ x.length := by omega
  have hk3 : (x.length + 6) / 7 ≤ 998 := by unfold MAXLEN at hl; omega
  have hd : dataBlock A x = blocks ((x.length + 6) / 7) 1001 (x.map (code A)) :=
    blocks_fuel _ _ _ _ hk2 (by simpa using hk1)
  have hlen := length_le_blocks ((x.length + 6) / 7) 1001 (x.map (code A)) (by simpa using hk1)
  unfold parseFile
  rw [hd, parseData_blocks c _ 1001 _ _ (by simpa using hk1)
    (by simp only [List.length_append, List.length_map] at hlen ⊢; omega) (by omega) hcodes]
  simp only [decodeCodes_map A hA x hx, Option.map_some]

/-! ## The code -/

def TAIL0 : Text := "O100CALL[0]\nM2".toList
def TAIL1 : Text := "O100CALL[1]\nM2".toList

/-- The mode of code of the form `pre O100CALL[m]⏎M2`. -/
def parseCode (pre c : Text) : Option Nat :=
  match stripPrefix pre c with
  | some r => if r = TAIL0 then some 0 else if r = TAIL1 then some 1 else none
  | none => none

theorem parseCode_tail0 (pre : Text) : parseCode pre (pre ++ TAIL0) = some 0 := by
  simp [parseCode, stripPrefix_append]

theorem parseCode_tail1 (pre : Text) : parseCode pre (pre ++ TAIL1) = some 1 := by
  simp [parseCode, stripPrefix_append, TAIL0, TAIL1]

/-! ## Substitution, quotation and the template -/

/-- `sub c x` stores `x` and runs the code `c`. -/
def sub (c x : Text) : Text := dataBlock A x ++ c

/-- The text that a file shows in mode `m` with stored text `x`. -/
def shown (m : Nat) (x : Text) : Text := if m = 1 then sub A x x else x

/-- A file that stores `t` and shows it. -/
def quoteWith (pre t : Text) : Text := dataBlock A t ++ (pre ++ TAIL0)

/-- The template: show the data block of the stored text, then the stored text. -/
def tmplWith (pre : Text) : Text := pre ++ TAIL1

end QuineEngine.NgcScript
