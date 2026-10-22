import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechTermDefs
import Submission.Work.ANALYTIC.CechPt.LevelDefs

/-!
# The level structure on the terms of the Čech nerve (definitions)

`Work.ANALYTIC.CechPt.cechTerm p` is the light profinite set of `(p+1)`-tuples of points of the
Cantor set `C = {0,1}^ℕ` with the same binary expansion (`CechTermDefs.lean`).

This module collects the elementary combinatorial gadgets used to exhibit `cechTerm p` as the
inverse limit of the finite sets `Level.lev (2^(n+1)) p` ("level-`n` dyadic nerves"):

* `digitsOf c : ℕ → Fin 2` is the digit sequence of a point `c` of the Cantor set (its `n`-th
  coordinate projection), so that `binExp c = Real.ofDigits (digitsOf c)`;
* `truncOf n d` is the integer with `(n+1)` binary digits `d 0, d 1, …, d n` (most significant
  first), i.e. `truncOf n d = ∑_{i ≤ n} d i * 2^(n-i)`.  Equivalently
  `truncOf n d = 2^(n+1) * (d 0/2 + d 1/4 + ⋯ + d n/2^(n+1))`;
* `truncVal n c = truncOf n (digitsOf c)` is the level-`n` truncation of a point of `C`.

The key relation to `Real.ofDigits` (`ofDigits_eq_truncOf_mul`,
`truncOf_le_mul_ofDigits`, `mul_ofDigits_le_truncOf_add_one`) is that

  `2^(n+1) * ofDigits d = truncOf n d + θ`   with  `θ = ofDigits (tail) ∈ [0,1]`,

so `|truncOf n d - truncOf n e| ≤ 1` whenever `ofDigits d = ofDigits e`.  This is what makes the
digit truncation land in the level-`n` dyadic nerve `Level.lev (2^(n+1)) p` (whose simplices are
tuples of diameter at most one).
-/

open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

/-- The digit sequence of a point of the Cantor set `C = {0,1}^ℕ` (its `n`-th coordinate). -/
def digitsOf (c : ↥cantor) : ℕ → Fin 2 := fun n => (coord n).hom.hom c

/-- The `k`-th digit of a point of the Cantor set. -/
def digit (k : ℕ) (c : ↥cantor) : Fin 2 := digitsOf c k

/-- `truncOf n d` is the natural number whose binary digits are `d 0, …, d n` (most significant
first), i.e. `∑_{i ≤ n} d i * 2^(n-i)`. -/
def truncOf (n : ℕ) (d : ℕ → Fin 2) : ℕ := ∑ i ∈ Finset.range (n + 1), (d i : ℕ) * 2 ^ (n - i)

/-- The level-`n` truncation of a point of the Cantor set: the first `n+1` binary digits, read as
a natural number in `{0, …, 2^(n+1)-1}`. -/
def truncVal (n : ℕ) (c : ↥cantor) : ℕ := truncOf n (digitsOf c)

lemma binExp_coe (c : ↥cantor) : (binExp c : ℝ) = Real.ofDigits (digitsOf c) := rfl

lemma truncVal_def (n : ℕ) (c : ↥cantor) : truncVal n c = truncOf n (digitsOf c) := rfl

open Finset in
/-- The recursion `truncOf (n+1) d = 2 * truncOf n d + d (n+1)`. -/
theorem truncOf_succ (n : ℕ) (d : ℕ → Fin 2) :
    truncOf (n + 1) d = 2 * truncOf n d + (d (n + 1) : ℕ) := by
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (d i : ℕ) * 2 ^ (n + 1 - i) = 2 * ((d i : ℕ) * 2 ^ (n - i)) := by
    intro i hi
    have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
    rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
    ring
  rw [truncOf, Finset.sum_range_succ, truncOf, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl hterm
  · rw [show n + 1 - (n + 1) = 0 by omega, pow_zero, mul_one]

/-- The truncated number is the last digit modulo `2`. -/
theorem truncOf_mod_two (n : ℕ) (d : ℕ → Fin 2) : truncOf n d % 2 = (d n : ℕ) := by
  induction n with
  | zero => simp [truncOf, Nat.mod_eq_of_lt (d 0).isLt]
  | succ n ih =>
    rw [truncOf_succ, show 2 * truncOf n d + (d (n + 1) : ℕ)
      = (d (n + 1) : ℕ) + 2 * truncOf n d by ring,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (d (n + 1)).isLt]

/-- The truncated number is bounded by `2^(n+1) - 1`. -/
theorem truncOf_lt (n : ℕ) (d : ℕ → Fin 2) : truncOf n d < 2 ^ (n + 1) := by
  induction n with
  | zero => simpa [truncOf] using (d 0).isLt
  | succ n ih =>
    rw [truncOf_succ]
    have h1 : (d (n + 1) : ℕ) ≤ 1 := by have := (d (n + 1)).isLt; omega
    have h2 : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; ring
    omega

/-- Dividing the level-`(n+1)` truncation by two gives the level-`n` truncation. -/
theorem truncOf_succ_div (n : ℕ) (d : ℕ → Fin 2) : truncOf (n + 1) d / 2 = truncOf n d := by
  rw [truncOf_succ, Nat.mul_add_div (show 2 > 0 by norm_num),
    Nat.div_eq_of_lt (d (n + 1)).isLt, Nat.add_zero]

end Work.ANALYTIC.CechPt
