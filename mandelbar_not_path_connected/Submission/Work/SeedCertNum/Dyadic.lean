/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# `Work.SeedCert.Dya`: exact dyadic rationals and their kernel-checkable comparisons

This file is the bottom layer (item **I** of the `SeedCertNum` contract,
`NOTES_LEAD_mandelbar_noncusp.md` §3.2) of the certified-numerics area of the mandelbar seed.

`Dya.mk m e` denotes the dyadic rational `m / 2^e`.  The representation is deliberately *not*
canonical (`⟨2, 1⟩` and `⟨1, 0⟩` denote the same real number): a canonical form would need `gcd`
computations that the kernel would have to run for every operation.  All arithmetic below is
exact — `add`, `neg`, `mul` do not round — and every *test* (`le`, `lt`, `pos`, `negb`, `nonneg`)
is a plain `Int` comparison after cross-multiplying by a power of two.  This is what makes a
`decide`-checked certificate of tens of thousands of interval operations feasible at all
(the kernel budget rule of the contract, item 0).

## Contents

* `Dya`, `Dya.toReal`, `ofInt`, `zero`, `one`, `two`;
* `add`, `neg`, `sub`, `mul`, `twice`, `half`, `isNeg`, `abs`, `min`, `max`, `maxAbs`;
* the ring lemmas `toReal_add`, `toReal_neg`, `toReal_sub`, `toReal_mul`, `toReal_twice`,
  `toReal_half`, `toReal_abs`, `toReal_min`, `toReal_max`;
* the test lemmas `toReal_le_iff`, `toReal_lt_iff`, `toReal_pos_iff`, `toReal_negb_iff`,
  `toReal_nonneg_iff`, with the coercion helpers `toReal_le_of_le`, `le_of_toReal_le`,
  `toReal_lt_of_lt`, `lt_of_toReal_lt`;
* the bound lemmas `toReal_le_maxAbs_left`, `toReal_le_maxAbs_right`, `maxAbs_nonneg`.

Nothing here mentions the tricorn; the tricorn enters in `CBox.lean`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

/-- An exact dyadic rational.  `Dya.mk m e` denotes `m / 2^e`; the representation is not
canonical. -/
structure Dya where
  num : ℤ
  exp : ℕ
deriving DecidableEq, Repr

namespace Dya

/-- The real number denoted by a dyadic. -/
noncomputable def toReal (a : Dya) : ℝ := (a.num : ℝ) / (2 : ℝ) ^ a.exp

theorem two_pow_pos (e : ℕ) : (0 : ℝ) < (2 : ℝ) ^ e := by positivity

@[simp] theorem toReal_mk (m : ℤ) (e : ℕ) :
    toReal ⟨m, e⟩ = (m : ℝ) / (2 : ℝ) ^ e := rfl

/-- The dyadic integer `n`. -/
def ofInt (n : ℤ) : Dya := ⟨n, 0⟩

/-- The dyadic rational `0`. -/
def zero : Dya := ⟨0, 0⟩

/-- The dyadic rational `1`. -/
def one : Dya := ⟨1, 0⟩

/-- The dyadic rational `2`. -/
def two : Dya := ⟨2, 0⟩

@[simp] theorem toReal_zero : zero.toReal = 0 := by simp [zero, toReal]
@[simp] theorem toReal_one : one.toReal = 1 := by simp [one, toReal]
@[simp] theorem toReal_two : two.toReal = 2 := by simp [two, toReal]
@[simp] theorem toReal_ofInt (n : ℤ) : (ofInt n).toReal = (n : ℝ) := by
  simp [ofInt, toReal]

/-- `n · 2^e`, computed with the kernel-primitive shift `Nat.shiftLeft`.  This matters: `decide`
on an interval certificate whose box recursion produces dyadics of exponent in the thousands
(item A1) would otherwise have to evaluate `2 ^ e` by a recursion of depth `e`, exhausting the
recursion depth (and memory) long before the certificate is checked.  `Nat.shiftLeft` is a
kernel primitive, so `1 <<< e` reduces in constant time in the *bits* of `e`. -/
def shl (n : ℤ) (e : ℕ) : ℤ := n * ((1 : ℕ) <<< e : ℤ)

theorem shl_eq (n : ℤ) (e : ℕ) : shl n e = n * 2 ^ e := by
  unfold shl
  rw [Nat.shiftLeft_eq]
  push_cast
  ring

/-- Exact addition: `m₁/2^{e₁} + m₂/2^{e₂}` over the common denominator `2^{e₁+e₂}`, via `shl`
(so that the kernel does not have to evaluate `2 ^ e` by a recursion of depth `e`). -/
def add (a b : Dya) : Dya := ⟨shl a.num b.exp + shl b.num a.exp, a.exp + b.exp⟩

/-- Exact negation. -/
def neg (a : Dya) : Dya := ⟨-a.num, a.exp⟩

/-- Exact subtraction. -/
def sub (a b : Dya) : Dya := add a (neg b)

/-- Exact multiplication: `m₁m₂/2^{e₁+e₂}`. -/
def mul (a b : Dya) : Dya := ⟨a.num * b.num, a.exp + b.exp⟩

/-- Doubling, kept separate from `mul two` so the kernel does not build the literal `⟨2,0⟩`. -/
def twice (a : Dya) : Dya := ⟨2 * a.num, a.exp⟩

/-- Halving. -/
def half (a : Dya) : Dya := ⟨a.num, a.exp + 1⟩

/-- The sign test `a < 0`, as a `Bool`. -/
def isNeg (a : Dya) : Bool := decide (a.num < 0)

/-- The absolute value, decided on the numerator. -/
def abs (a : Dya) : Dya := match isNeg a with | true => neg a | false => a

theorem toReal_add (a b : Dya) : (add a b).toReal = a.toReal + b.toReal := by
  simp only [add, toReal, shl_eq]
  push_cast
  rw [pow_add]
  field_simp

theorem toReal_neg (a : Dya) : (neg a).toReal = -a.toReal := by
  simp only [neg, toReal]
  push_cast
  ring

theorem neg_neg (a : Dya) : neg (neg a) = a := by
  cases a with
  | mk m e => simp [neg]

theorem toReal_sub (a b : Dya) : (sub a b).toReal = a.toReal - b.toReal := by
  simp only [sub, toReal_add, toReal_neg]
  ring

theorem toReal_mul (a b : Dya) : (mul a b).toReal = a.toReal * b.toReal := by
  simp only [mul, toReal]
  push_cast
  rw [pow_add]
  ring

theorem toReal_twice (a : Dya) : (twice a).toReal = 2 * a.toReal := by
  simp only [twice, toReal]
  push_cast
  ring

theorem toReal_half (a : Dya) : (half a).toReal = a.toReal / 2 := by
  simp only [half, toReal]
  rw [pow_succ]
  ring

theorem toReal_isNeg (a : Dya) : isNeg a = true ↔ a.toReal < 0 := by
  simp only [isNeg, decide_eq_true_eq, toReal]
  rw [div_lt_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ a.exp by positivity), zero_mul]
  exact_mod_cast Iff.rfl

theorem toReal_abs (a : Dya) : (abs a).toReal = |a.toReal| := by
  by_cases h : isNeg a = true
  · have hh : a.num < 0 := by simpa [isNeg] using h
    rw [abs, h, toReal_neg, abs_of_neg]
    simp only [toReal]
    exact div_neg_of_neg_of_pos (by exact_mod_cast hh) (by positivity)
  · have hh : ¬ a.num < 0 := by simpa [isNeg] using h
    have hf : isNeg a = false := Bool.eq_false_iff.mpr h
    rw [abs, hf, abs_of_nonneg]
    simp only [toReal]
    exact div_nonneg (by exact_mod_cast (not_lt.mp hh)) (by positivity)

/-! ## The kernel-checkable tests -/

/-- `a ≤ b` for dyadics, decided by cross-multiplying by `2^{a.exp + b.exp}` (via `shl`, so that
the cost is independent of the exponents). -/
def le (a b : Dya) : Bool := decide (shl a.num b.exp ≤ shl b.num a.exp)

/-- `a < b` for dyadics. -/
def lt (a b : Dya) : Bool := decide (shl a.num b.exp < shl b.num a.exp)

/-- `0 < a`. -/
def pos (a : Dya) : Bool := decide (0 < a.num)

/-- `a < 0`. -/
def negb (a : Dya) : Bool := decide (a.num < 0)

/-- `0 ≤ a`. -/
def nonneg (a : Dya) : Bool := decide (0 ≤ a.num)

theorem toReal_pos_iff (a : Dya) : pos a = true ↔ 0 < a.toReal := by
  simp only [pos, decide_eq_true_eq, toReal]
  rw [lt_div_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ a.exp by positivity), zero_mul]
  exact_mod_cast Iff.rfl

theorem toReal_negb_iff (a : Dya) : negb a = true ↔ a.toReal < 0 := by
  simp only [negb, decide_eq_true_eq, toReal]
  rw [div_lt_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ a.exp by positivity), zero_mul]
  exact_mod_cast Iff.rfl

theorem toReal_nonneg_iff (a : Dya) : nonneg a = true ↔ 0 ≤ a.toReal := by
  simp only [nonneg, decide_eq_true_eq, toReal]
  rw [le_div_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ a.exp by positivity), zero_mul]
  exact_mod_cast Iff.rfl

theorem toReal_le_iff (a b : Dya) : le a b = true ↔ a.toReal ≤ b.toReal := by
  simp only [le, decide_eq_true_eq, toReal, shl_eq]
  rw [div_le_div_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ a.exp by positivity)
      (show (0 : ℝ) < (2 : ℝ) ^ b.exp by positivity)]
  constructor
  · intro h; exact_mod_cast h
  · intro h
    rw [show (a.num : ℝ) * (2 : ℝ) ^ b.exp = ((a.num * (2 : ℤ) ^ b.exp : ℤ) : ℝ) by
          push_cast; ring,
        show (b.num : ℝ) * (2 : ℝ) ^ a.exp = ((b.num * (2 : ℤ) ^ a.exp : ℤ) : ℝ) by
          push_cast; ring] at h
    exact_mod_cast h

theorem toReal_lt_iff (a b : Dya) : lt a b = true ↔ a.toReal < b.toReal := by
  simp only [lt, decide_eq_true_eq, toReal, shl_eq]
  rw [div_lt_div_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ a.exp by positivity)
      (show (0 : ℝ) < (2 : ℝ) ^ b.exp by positivity)]
  constructor
  · intro h; exact_mod_cast h
  · intro h
    rw [show (a.num : ℝ) * (2 : ℝ) ^ b.exp = ((a.num * (2 : ℤ) ^ b.exp : ℤ) : ℝ) by
          push_cast; ring,
        show (b.num : ℝ) * (2 : ℝ) ^ a.exp = ((b.num * (2 : ℤ) ^ a.exp : ℤ) : ℝ) by
          push_cast; ring] at h
    exact_mod_cast h

theorem le_of_toReal_le {a b : Dya} (h : a.toReal ≤ b.toReal) : le a b = true :=
  (toReal_le_iff a b).mpr h

theorem toReal_le_of_le {a b : Dya} (h : le a b = true) : a.toReal ≤ b.toReal :=
  (toReal_le_iff a b).mp h

theorem lt_of_toReal_lt {a b : Dya} (h : a.toReal < b.toReal) : lt a b = true :=
  (toReal_lt_iff a b).mpr h

theorem toReal_lt_of_lt {a b : Dya} (h : lt a b = true) : a.toReal < b.toReal :=
  (toReal_lt_iff a b).mp h

/-- `min` of two dyadics. -/
def min (a b : Dya) : Dya := match le a b with | true => a | false => b

/-- `max` of two dyadics. -/
def max (a b : Dya) : Dya := match le a b with | true => b | false => a

theorem toReal_min (a b : Dya) : (min a b).toReal = Min.min a.toReal b.toReal := by
  by_cases h : le a b = true
  · rw [min, h, min_eq_left ((toReal_le_iff a b).mp h)]
  · have h' : ¬ a.toReal ≤ b.toReal := fun hc => absurd ((toReal_le_iff a b).mpr hc) h
    have hh : le a b = false := Bool.eq_false_iff.mpr h
    rw [min, hh, min_eq_right (le_of_lt (not_le.mp h'))]

theorem toReal_max (a b : Dya) : (max a b).toReal = Max.max a.toReal b.toReal := by
  by_cases h : le a b = true
  · rw [max, h, max_eq_right ((toReal_le_iff a b).mp h)]
  · have h' : ¬ a.toReal ≤ b.toReal := fun hc => absurd ((toReal_le_iff a b).mpr hc) h
    have hh : le a b = false := Bool.eq_false_iff.mpr h
    rw [max, hh, max_eq_left (le_of_lt (not_le.mp h'))]

/-- The upper bound `max |a| |b|`, used as `|x| ≤ ·` when `a ≤ x ≤ b`. -/
def maxAbs (a b : Dya) : Dya := max (abs a) (abs b)

/-- The element of the interval `[a,b]` closest to `0`; a lower bound for `|x|` when
`a ≤ x ≤ b`. -/
def minAbs (a b : Dya) : Dya := max a (min b zero)

theorem toReal_minAbs (a b : Dya) :
    (minAbs a b).toReal = Max.max a.toReal (Min.min b.toReal 0) := by
  simp [minAbs, toReal_max, toReal_min, toReal_zero]

/-- `minAbs a b` is a lower bound for `|x|` when `a ≤ x ≤ b`. -/
theorem minAbs_le_abs {a b : Dya} {x : ℝ} (hab : a.toReal ≤ b.toReal)
    (hax : a.toReal ≤ x) (hxb : x ≤ b.toReal) : (minAbs a b).toReal ≤ |x| := by
  rw [toReal_minAbs]
  rcases le_total 0 a.toReal with h | h
  · rw [max_le_iff]
    exact ⟨le_trans hax (le_abs_self x), le_trans (min_le_right _ _) (abs_nonneg x)⟩
  · rcases le_total 0 b.toReal with h2 | h2
    · rw [min_eq_right h2, max_eq_right h]
      exact abs_nonneg x
    · rw [min_eq_left h2, max_eq_right hab]
      exact le_trans h2 (abs_nonneg x)

/-- `minAbs a b ≤ |b|` and `minAbs a b ≤ |a|`-form: a lower bound for `|x|` is at most the
endpoint moduli. -/
theorem minAbs_le_abs_of_mem {a b : Dya} {x : ℝ} (hab : a.toReal ≤ b.toReal)
    (hax : a.toReal ≤ x) (hxb : x ≤ b.toReal) : (minAbs a b).toReal ≤ |x| :=
  minAbs_le_abs hab hax hxb

end Dya

end Work.SeedCert
