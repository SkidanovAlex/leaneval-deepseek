import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux

/-!
# Shared definitions for `Work.HP.window_sum_r2`

`window_sum_r2` bounds the sum, over a finite family `T` of primitive rank-`2`
lattices `L ⊆ ℤ^{n+1}` with `detL L ≤ Δ + 1`, `lam L 1 ≤ X`, `lam L 2 ≤ Y`, of the
product `ballCount L X * ballCount L Y`.

The proof groups the lattices by the dyadic window `kwin 2 L : Fin 2 → ℕ` of their
successive minima, counts the lattices in each window by `hnum`, bounds each ball
product by the bilinear window bound `hbp`, and finally compares with the
arithmetic input `harith`.

This file fixes the notation used by both the main proof and the delegated
children:

* `winM Kmink Δ` — the window bound `⌈log₂ (4 Kmink (Δ+1))⌉`;
* `winE n j` — the exponent with which the `j`-th window coordinate is counted,
  namely `n + 1 + 2 + 1 - 2 (j+1)`;
* `winBp Ksmall X Y k` — the product of the two ball count bounds at window `k`;
* `winS n X Y k` — the three-term arithmetic summand at window `k`;
* `winSum n X Y M k` — `winS` cut off by the four window conditions.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

/-- The dyadic window bound `⌈log₂ (4 Kmink (Δ+1))⌉`. -/
def winM (Kmink Δ : ℝ) : ℕ := ⌈Real.logb 2 ((2 : ℝ) ^ 2 * Kmink * (Δ + 1))⌉₊

/-- Exponent with which the `j`-th successive minimum is counted, in rank `2`:
`n + 1 + 2 + 1 - 2 * (j.1 + 1)`. -/
def winE (n : ℕ) (j : Fin 2) : ℕ := n + 1 + 2 + 1 - 2 * (j.1 + 1)

/-- The product of the two ball-count bounds at a dyadic window `k`, exactly as it
appears in `hbp`. -/
def winBp (Ksmall X Y : ℝ) (k : Fin 2 → ℕ) : ℝ :=
  Ksmall ^ 2 * (16 * X ^ 2 * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (2 * k 1))
    + 8 * X * Y ^ 2 / ((2 : ℝ) ^ (2 * k 0) * (2 : ℝ) ^ (k 1))
    + 4 * Y ^ 2 / ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)))

/-- The three-term arithmetic summand of `harith` at a dyadic window `k`. -/
def winS (n : ℕ) (X Y : ℝ) (k : Fin 2 → ℕ) : ℝ :=
  X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
    + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
    + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)

/-- The summand of the arithmetic sum, cut off by the four window conditions. -/
def winSum (n : ℕ) (X Y : ℝ) (M : ℕ) (k : Fin 2 → ℕ) : ℝ :=
  if Monotone k ∧ (∑ j, k j) ≤ M ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y then
    X ^ 2 * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 3) * k 1)
      + X * Y ^ 2 * (2 : ℝ) ^ ((n + 1 - 1) * k 0 + (n + 1 - 2) * k 1)
      + Y ^ 2 * (2 : ℝ) ^ ((n + 1) * k 0 + (n + 1 - 2) * k 1)
  else 0

/-- The four window conditions, as a predicate on `k : Fin 2 → ℕ`. -/
def winCond (X Y : ℝ) (M : ℕ) (k : Fin 2 → ℕ) : Prop :=
  Monotone k ∧ (∑ j, k j) ≤ M ∧ (2 : ℝ) ^ (k 0) ≤ 2 * X ∧ (2 : ℝ) ^ (k 1) ≤ 2 * Y

lemma winSum_eq_winS {n : ℕ} {X Y : ℝ} {M : ℕ} {k : Fin 2 → ℕ} (h : winCond X Y M k) :
    winSum n X Y M k = winS n X Y k := by
  simp only [winSum, winS, winCond] at h ⊢
  rw [if_pos h]

lemma winSum_eq_zero {n : ℕ} {X Y : ℝ} {M : ℕ} {k : Fin 2 → ℕ} (h : ¬ winCond X Y M k) :
    winSum n X Y M k = 0 := by
  simp only [winSum, winCond] at h ⊢
  exact if_neg h

lemma winE_zero (n : ℕ) : winE n 0 = n + 2 := by
  rw [winE]; omega

lemma winE_one (n : ℕ) : winE n 1 = n := by
  rw [winE]; omega

end Work.HP
