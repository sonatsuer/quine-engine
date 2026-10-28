import QuineEngine.Engine

/-!
# Underload

Underload (https://esolangs.org/wiki/Underload) is a small, Turing-complete esoteric language.
A program is a string of one-character commands acting on a stack of strings, which are
themselves programs. It is concatenative: running `xy` is running `x` and then `y`.

Commands: `(…)` push literal, `:` dup, `!` drop, `~` swap, `*` concat,
`a` wrap in parens, `S` print, `^` eval. Texts are `List Char`.

This file implements an interpreter, plugs Underload into the engine, and obtains the quine
`(:aSS):aSS` with a proof that it prints itself.
-/

namespace QuineEngine.Underload

/-- Paren depth walk; `none` if the depth goes negative. -/
def walk : Nat → List Char → Option Nat
  | d, [] => some d
  | d, c :: r =>
    if c = '(' then walk (d + 1) r
    else if c = ')' then (match d with | 0 => none | d + 1 => walk d r)
    else walk d r

/-- Read a literal up to its matching `)`. -/
def parseLit : Nat → List Char → List Char → Option (List Char × List Char)
  | _, _, [] => none
  | d, acc, c :: r =>
    if c = '(' then parseLit (d + 1) (c :: acc) r
    else if c = ')' then (match d with | 0 => some (acc.reverse, r) | d + 1 => parseLit d (c :: acc) r)
    else parseLit d (c :: acc) r

/-- Interpreter with fuel. -/
def exec : Nat → List Char → List (List Char) → List Char → Option (List Char)
  | 0, _, _, _ => none
  | _ + 1, [], _, out => some out
  | n + 1, c :: r, st, out =>
    if c = '(' then
      match parseLit 0 [] r with
      | some (s, r') => exec n r' (s :: st) out
      | none => none
    else match c, st with
      | ':', s :: st => exec n r (s :: s :: st) out
      | '!', _ :: st => exec n r st out
      | '~', x :: y :: st => exec n r (y :: x :: st) out
      | '*', x :: y :: st => exec n r ((y ++ x) :: st) out
      | 'a', s :: st => exec n r (('(' :: s ++ [')']) :: st) out
      | 'S', s :: st => exec n r st (out ++ s)
      | '^', s :: st => exec n (s ++ r) st out
      | _, _ => none

/-- Program `t` terminates printing `out`. -/
def Runs (t out : List Char) : Prop := ∃ n, exec n t [] [] = some out

def Balanced (x : List Char) : Prop := walk 0 x = some 0

instance (x : List Char) : Decidable (Balanced x) := inferInstanceAs (Decidable (_ = _))

theorem walk_append (d : Nat) (x y : List Char) :
    walk d (x ++ y) = (walk d x).bind (fun e => walk e y) := by
  induction x generalizing d with
  | nil => simp [walk]
  | cons c r ih =>
    simp only [List.cons_append, walk]
    split
    · exact ih _
    · split
      · cases d <;> simp [ih]
      · exact ih _

theorem walk_shift (k : Nat) : ∀ (d e : Nat) (x : List Char),
    walk d x = some e → walk (d + k) x = some (e + k) := by
  intro d e x
  induction x generalizing d with
  | nil => simp [walk]
  | cons c r ih =>
    simp only [walk]
    split
    · intro h; have := ih _ h; rwa [Nat.add_right_comm]
    · split
      · cases d with
        | zero => simp
        | succ d => intro h; have := ih _ h; rwa [Nat.add_right_comm]
      · exact ih _

theorem parseLit_balanced (rest : List Char) : ∀ (x : List Char) (d : Nat) (acc : List Char),
    walk d x = some 0 → parseLit d acc (x ++ ')' :: rest) = some (acc.reverse ++ x, rest) := by
  intro x
  induction x with
  | nil => intro d acc h; simp [walk] at h; subst h; simp [parseLit]
  | cons c r ih =>
    intro d acc h
    simp only [List.cons_append, parseLit]
    by_cases h1 : c = '('
    · subst h1
      simp only [walk, if_true] at h
      simp only [if_true]; rw [ih _ _ h]; simp
    · by_cases h2 : c = ')'
      · subst h2
        cases d with
        | zero => simp [walk] at h
        | succ d =>
          simp [walk] at h
          simp only [if_neg h1, if_true]; rw [ih _ _ h]; simp
      · simp only [walk, if_neg h1, if_neg h2] at h
        simp only [if_neg h1, if_neg h2]; rw [ih _ _ h]; simp

/-- Printing a balanced literal: `(t)S` prints `t`. -/
theorem runs_print (t : List Char) (h : Balanced t) :
    exec 3 ('(' :: (t ++ [')', 'S'])) [] [] = some t := by
  have hp := parseLit_balanced ['S'] t 0 [] h
  simp only [List.reverse_nil, List.nil_append] at hp
  simp [exec, hp]

/-- The duplicating template: `(x):aSS` prints `(x)x`. -/
theorem runs_dup (x : List Char) (h : Balanced x) :
    exec 6 ('(' :: (x ++ ')' :: [':', 'a', 'S', 'S'])) [] [] = some ('(' :: (x ++ ')' :: x)) := by
  have hp := parseLit_balanced [':', 'a', 'S', 'S'] x 0 [] h
  simp only [List.reverse_nil, List.nil_append] at hp
  simp [exec, hp]

theorem balanced_dup (x : List Char) (h : Balanced x) : Balanced ('(' :: (x ++ ')' :: x)) := by
  unfold Balanced at *
  have h1 := walk_shift 1 0 0 x h
  simp only [walk, Nat.zero_add, walk_append, h1, Option.bind_some] at *
  simp [h]

/-! ## Plugging Underload into the engine -/

/-- Display = what the program prints. Scanning is trivial here (classical quines). -/
def system : System (List Char) (List Char) where
  disp := Runs
  scan := some
  render := id
  scan_render := fun _ => rfl

def quotation : Quotation system where
  Dom := Balanced
  q := fun t => '(' :: (t ++ [')', 'S'])
  disp_q := fun t h => ⟨t, ⟨3, runs_print t h⟩, rfl⟩

/-- Every program prints at most one thing (needed to transfer meanings). -/
theorem exec_det : ∀ (n m : Nat) (t : List Char) (st : List (List Char)) (o o1 o2 : List Char),
    exec n t st o = some o1 → exec m t st o = some o2 → o1 = o2 := by
  intro n
  induction n with
  | zero => intro m t st o o1 o2 h; simp [exec] at h
  | succ n ih =>
    intro m t st o o1 o2 h1 h2
    cases m with
    | zero => simp [exec] at h2
    | succ m =>
      cases t with
      | nil => simp [exec] at h1 h2; rw [← h1, ← h2]
      | cons c r =>
        simp only [exec] at h1 h2
        split at h1
        · rw [if_pos ‹_›] at h2
          split at h1 <;> simp_all
          rename_i s r' _
          exact ih m _ _ _ _ _ h1 h2
        · rw [if_neg ‹_›] at h2
          split at h1 <;> simp only at h2 <;> (try simp at h1) <;> exact ih m _ _ _ _ _ h1 h2

def diagonal : Diagonal system quotation where
  sub := fun a x => '(' :: (x ++ ')' :: a)
  a := [':', 'a', 'S', 'S']
  Ok := Balanced
  spec := by
    intro x hx s ⟨p, ⟨n, hn⟩, hs⟩
    simp only [system, Option.some.injEq] at hs
    subst hs
    have h1 := runs_print _ (balanced_dup x hx)
    have := exec_det _ _ _ _ _ _ _ hn h1
    subst this
    exact ⟨_, ⟨6, runs_dup x hx⟩, rfl⟩

/-- The engine's output. -/
def quine : List Char := diagonal.quine

theorem quine_correct : system.IsQuine quine :=
  diagonal.isQuine (show Balanced [':', 'a', 'S', 'S'] by decide) (show Balanced quine by decide)

#eval String.mk quine

end QuineEngine.Underload
