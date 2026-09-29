import Mathlib
import Submission.Work.IntLib.SqrtGcd.GcdProg
import Submission.Work.IntLib.SqrtGcd.oddPartSpec

/-!
# Binary gcd (`SG.gcdMain`): shared vocabulary

The main loop `SG.gcdMain` implements the binary gcd on the raw bit regions
`sU`, `sV` of the stack layout of `GcdProg.lean`.  This file collects the definitions used by the
correctness proof of `gcdMain`:

* `BitsAt k T l below s` — the region of stack `k` above its marker `T` is the least-significant
  bit first bit list `l`, with `below` sitting under the marker;
* `GSt ... s u v` — the state invariant: `sU` holds `u`, `sV` holds `v` (both odd), the scratch
  stacks `sP, sQ, sR, sS` hold nothing above their markers, `sG` and all other stacks are
  untouched;
* `gNext u v` — one iteration of the gcd: the pair stays put if `u = v` (the loop then stops),
  otherwise it is `SG.gcdStep u v`;
* `nFalses` / `dropFalses` — the number of leading `false` bits of a bit list, and the list with
  them removed.  Reading them from the top of a *most significant first* region strips the high
  zeros (zero test), and from the top of a *least significant first* region strips the low zeros
  (odd part).

Notation: a bit list is least significant bit first unless it is a region being read most
significant first (as in `SG.bval`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib.SqrtGcd

open HvdH Work.IntLib
open Work.IntLib.SG

/-- `BitsAt k T l below s`: the region of stack `k` above its marker `T` is the bit list `l`
(least significant bit first, `l.head` on top), with `below` sitting under the marker. -/
def BitsAt (k : Stk) (T : Glyph) (l : List Bool) (below : List Glyph) (s : State) : Prop :=
  s.stk k = l.map Glyph.bit ++ T :: below

/-- Invariant of the binary-gcd loop `SG.gcdMain`: the two operands sit in `sU`, `sV` (odd, of
bit length at most `N`), the four scratch stacks `sP … sS` are empty above their markers, and
everything else (in particular `sG` and all stacks other than `sU … sS`) is as in `s₀`. -/
structure GSt (N : ℕ) (bU bV bP bQ bR bS : List Glyph) (s₀ s : State) (u v : ℕ) : Prop where
  hU : ∃ ul : List Bool, BitsAt sU (Glyph.mk sU) ul bU s ∧ ofBits ul = u ∧ ul.length ≤ N
  hV : ∃ vl : List Bool, BitsAt sV (Glyph.mk sV) vl bV s ∧ ofBits vl = v ∧ vl.length ≤ N
  hoddU : u % 2 = 1
  hoddV : v % 2 = 1
  hP : BitsAt sP (Glyph.mk sP) [] bP s
  hQ : BitsAt sQ (Glyph.mk sQ) [] bQ s
  hR : BitsAt sR (Glyph.mk sR) [] bR s
  hS : BitsAt sS (Glyph.mk sS) [] bS s
  hG : s.stk sG = s₀.stk sG
  hfr : ∀ j : Stk, j ≠ sU → j ≠ sV → j ≠ sG → j ≠ sP → j ≠ sQ → j ≠ sR → j ≠ sS →
    s.stk j = s₀.stk j

/-- One iteration of the binary gcd: if `u = v` the pair stays and the loop stops, otherwise
the pair becomes `SG.gcdStep u v`. -/
def gNext (u v : ℕ) : ℕ × ℕ := if u = v then (u, v) else SG.gcdStep u v

/-! ## Leading `false` bits -/

/-- The number of leading `false` bits of a bit list. -/
def nFalses : List Bool → ℕ
  | [] => 0
  | true :: _ => 0
  | false :: l => nFalses l + 1

/-- The bit list with its leading `false` bits removed. -/
def dropFalses : List Bool → List Bool
  | [] => []
  | true :: l => true :: l
  | false :: l => dropFalses l

/-- The leading `false` bits of `l` are exactly the ones removed by `dropFalses`. -/
theorem replicate_nFalses_dropFalses (l : List Bool) :
    List.replicate (nFalses l) false ++ dropFalses l = l := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | true => rfl
    | false =>
      show List.replicate (nFalses t + 1) false ++ dropFalses t = false :: t
      rw [List.replicate_succ, List.cons_append, ih]

/-- `dropFalses l` is either empty or starts with a `true`. -/
theorem dropFalses_eq_nil_or_head_true (l : List Bool) :
    dropFalses l = [] ∨ ∃ l', dropFalses l = true :: l' := by
  induction l with
  | nil => exact Or.inl rfl
  | cons b t ih =>
    cases b with
    | true => exact Or.inr ⟨t, rfl⟩
    | false => exact ih

/-- Dropping leading `false` bits does not increase the length. -/
theorem length_dropFalses_le (l : List Bool) : (dropFalses l).length ≤ l.length := by
  induction l with
  | nil => simp [dropFalses]
  | cons b t ih =>
    cases b with
    | true => simp [dropFalses]
    | false => simp only [dropFalses, List.length_cons]; omega

/-- Dropping leading `false` bits does not change the most-significant-first value `SG.bval`. -/
theorem bval_dropFalses (l : List Bool) : SG.bval (dropFalses l) = SG.bval l := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    cases b with
    | true => rfl
    | false => simp only [dropFalses, bval_cons, Bool.toNat_false, mul_zero, add_zero]; exact ih

/-- A most-significant-first bit list has value zero exactly when it has no non-`false` bit. -/
theorem bval_eq_zero_iff (l : List Bool) : SG.bval l = 0 ↔ dropFalses l = [] := by
  constructor
  · intro h
    rcases dropFalses_eq_nil_or_head_true l with h' | ⟨l', h'⟩
    · exact h'
    · rw [← bval_dropFalses] at h
      rw [h'] at h
      have hb : SG.bval (true :: l') = SG.bval l' + 2 ^ l'.length := by
        simp [SG.bval_cons]
      have hpos : 0 < 2 ^ l'.length := pow_pos (by norm_num) _
      have hz : SG.bval l' + 2 ^ l'.length = 0 := by rw [← hb]; exact h
      omega
  · intro h
    rw [← bval_dropFalses, h]
    rfl

/-- `ofBits` of a list of `false`s is zero. -/
theorem ofBits_replicate_false_gcdInvDefs (k : ℕ) : ofBits (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ofBits_cons, ih, mul_zero, add_zero]
    rfl

/-- `oddPart (2 * m) = oddPart m`. -/
theorem oddPart_two_mul (m : ℕ) : oddPart (2 * m) = oddPart m := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · simp [h0]
  · rw [oddPart.eq_def, if_pos ⟨by omega, by omega⟩]
    have h2 : 2 * m / 2 = m := by
      omega
    rw [h2]

/-- Dropping the leading `false` bits of a least-significant-first bit list computes its odd
part. -/
theorem ofBits_dropFalses (l : List Bool) : ofBits (dropFalses l) = oddPart (ofBits l) := by
  induction l with
  | nil => rw [dropFalses, ofBits]; exact (oddPart_zero).symm
  | cons b t ih =>
    cases b with
    | true =>
      simp only [dropFalses]
      refine (oddPart_self ?_).symm
      rw [ofBits_cons]
      show (1 + 2 * ofBits t) % 2 = 1
      omega
    | false =>
      simp only [dropFalses, ofBits_cons, Bool.toNat_false, zero_add]
      rw [ih]
      exact (oddPart_two_mul (ofBits t)).symm

/-- A least-significant-first bit list has value zero exactly when it has no `true` bit. -/
theorem ofBits_eq_zero_iff (l : List Bool) : ofBits l = 0 ↔ dropFalses l = [] := by
  constructor
  · intro h
    induction l with
    | nil => rfl
    | cons b t ih =>
      cases b with
      | true =>
        exfalso
        have h1 : ofBits (true :: t) = 1 + 2 * ofBits t := by
          simp only [ofBits_cons, Bool.toNat_true]
        rw [h1] at h
        omega
      | false =>
        simp only [dropFalses]
        apply ih
        have h1 : ofBits (false :: t) = 2 * ofBits t := by
          simp only [ofBits_cons, Bool.toNat_false, zero_add]
        rw [h1] at h
        omega
  · intro h
    have h2 : l = List.replicate (nFalses l) false ++ dropFalses l :=
      (replicate_nFalses_dropFalses l).symm
    rw [h2, h, List.append_nil]
    exact ofBits_replicate_false_gcdInvDefs _

end Work.IntLib.SqrtGcd
