import Mathlib
import Submission.Work.HP.Defs

/-!
# Definitions for `Work.HP.dyadic_sum_r2`

The target `Work.HP.dyadic_sum_r2` bounds a dyadic sum over monotone `k : Fin 2 → ℕ`
whose entries are bounded by `2 ^ k ≤ 2 * X` etc.  We isolate here the summand and
the reduced (pair-indexed) versions, so that the different combinatorial pieces can
be proved in separate modules.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP

/-- The summand appearing in `dyadic_sum_r2`. -/
def dSummand (N : ℕ) (X Y : ℝ) (M : ℕ) (k : Fin 2 → ℕ) : ℝ :=
  if Monotone k ∧ (∑ j, k j) ≤ M ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
    X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 1) * k 0 + (N - 3) * k 1)
      + X * Y ^ 2 * (2 : ℝ) ^ ((N - 1) * k 0 + (N - 2) * k 1)
      + Y ^ 2 * (2 : ℝ) ^ (N * k 0 + (N - 2) * k 1)
  else 0

/-- The same summand, evaluated on a pair `(a, b) = (k 0, k 1)` and with the exponents
rewritten in terms of `s = a + b`. -/
def dPair (N : ℕ) (X Y : ℝ) (M : ℕ) (a b : ℕ) : ℝ :=
  if a ≤ b ∧ a + b ≤ M ∧ (2 : ℝ) ^ a ≤ 2 * X ∧ (2 : ℝ) ^ b ≤ 2 * Y then
    X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 3) * (a + b) + 2 * a)
      + X * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * (a + b) + a)
      + Y ^ 2 * (2 : ℝ) ^ ((N - 2) * (a + b) + 2 * a)
  else 0

/-- The index set of the inner sum for a fixed value `s` of `a + b`. -/
def dFib (s : ℕ) (X Y : ℝ) : Finset ℕ :=
  (Finset.range (s + 1)).filter
    (fun a => a ≤ s - a ∧ (2 : ℝ) ^ a ≤ 2 * X ∧ (2 : ℝ) ^ (s - a) ≤ 2 * Y)

/-- The three terms of `dPair` restricted to a fixed `s = a + b`. -/
def dGeo (N : ℕ) (X Y : ℝ) (s a : ℕ) : ℝ :=
  X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((N - 3) * s + 2 * a)
    + X * Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s + a)
    + Y ^ 2 * (2 : ℝ) ^ ((N - 2) * s + 2 * a)

end Work.HP
