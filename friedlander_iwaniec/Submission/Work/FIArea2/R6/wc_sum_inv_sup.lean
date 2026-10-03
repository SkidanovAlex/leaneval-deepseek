import Mathlib
import Submission.Work.FIArea2.R6.WCbasicDefs

/-!
# Layer-cake identity for the sup-norm weight

`Work.FIArea2.R6.wc_sum_inv_sup`: for a finite set `W` of nonzero integer vectors, all of
sup-norm at most `r` (`1 ≤ r`),

  `Σ_{w∈W} 1/|w|∞ = Σ_{t=1}^{r} #{w ∈ W : |w|∞ ≤ t}/(t(t+1)) + #W/(r+1)`.

PROOF ROUTE: expand each cardinality as a sum of indicators over `W`, exchange the two
finite sums (`Finset.sum_comm`), and telescope `Σ_{t=m}^{r} 1/(t(t+1)) = 1/m - 1/(r+1)`
using `1/(t(t+1)) = 1/t - 1/(t+1)` (`Finset.sum_Icc_sub`). Each `w` contributes to the
inner sum precisely for `t ∈ Icc (wcSup w) r`, i.e. `#{w ∈ W : wcSup w ≤ t}` terms.
-/

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

-- `hr` is genuinely redundant (`w ∈ W` already forces `1 ≤ r` via `hbox`), but it is part of
-- the requested statement, so we keep it and simply silence the unused-variable linter.
set_option linter.unusedVariables false

/-- A nonzero integer vector has sup-norm at least `1`. -/
lemma wcSup_pos_of_ne_zero {w : ℤ × ℤ} (hw : w ≠ 0) : 1 ≤ wcSup w := by
  rw [wcSup]
  rcases w with ⟨a, b⟩
  have hor : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (Prod.ext h.1 h.2)
  rcases hor with h | h
  · have := Int.natAbs_pos.mpr h; omega
  · have := Int.natAbs_pos.mpr h; omega

/-- Telescoping: `Σ_{t=m}^{r} 1/(t(t+1)) = 1/m - 1/(r+1)` for `1 ≤ m ≤ r`. -/
lemma wc_sum_inv_sup_telescope (m r : ℕ) (hm : 1 ≤ m) (hmr : m ≤ r) :
    ∑ t ∈ Finset.Icc m r, (1 : ℝ) / ((t : ℝ) * ((t : ℝ) + 1))
      = 1 / (m : ℝ) - 1 / ((r : ℝ) + 1) := by
  -- `1/(t(t+1)) = -(1/(t+1)) - -(1/t)`, the increment of `f i = -1/i`.
  have hsub : ∀ t ∈ Finset.Icc m r,
      (1 : ℝ) / ((t : ℝ) * ((t : ℝ) + 1)) = -(1 / ((t : ℝ) + 1)) - -(1 / (t : ℝ)) := by
    intro t ht
    have ht1 : (1 : ℕ) ≤ t := by
      have := (Finset.mem_Icc.mp ht).1
      omega
    have ht0 : (t : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
      linarith
    have ht1' : (t : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl hsub]
  have key := Finset.sum_Icc_sub hmr (fun i : ℕ => -(1 / (i : ℝ)))
  simp only [Nat.cast_add, Nat.cast_one] at key ⊢
  rw [key]
  ring

/-- **Layer-cake identity for the sup-norm weight.**

For a finite set `W` of nonzero integer vectors all of sup-norm at most `r` (`1 ≤ r`),

  `Σ_{w∈W} 1/|w|∞ = Σ_{t=1}^{r} #{w ∈ W : |w|∞ ≤ t}/(t(t+1)) + #W/(r+1)`.

PROOF ROUTE: for `1 ≤ m ≤ r`, telescope `Σ_{t=m}^{r} 1/(t(t+1)) = 1/m - 1/(r+1)` using
`1/(t(t+1)) = 1/t - 1/(t+1)`; sum over `w ∈ W` and exchange the two finite sums
(`Finset.sum_comm` / `Finset.sum_sigma`), noting `w` contributes to the inner sum precisely for
`t ∈ Icc (wcSup w) r`, i.e. `#{w ∈ W : wcSup w ≤ t}` terms for each `t`. -/
theorem wc_sum_inv_sup (r : ℕ) (hr : 1 ≤ r) (W : Finset (ℤ × ℤ))
    (hne : ∀ w ∈ W, w ≠ 0) (hbox : ∀ w ∈ W, wcSup w ≤ r) :
    ∑ w ∈ W, (1 : ℝ) / (wcSup w : ℝ)
      = ∑ t ∈ Finset.Icc 1 r, ((W.filter (fun w => wcSup w ≤ t)).card : ℝ)
          / ((t : ℝ) * ((t : ℝ) + 1))
        + (W.card : ℝ) / ((r : ℝ) + 1) := by
  -- Each layer cardinality is the sum of the indicator over `W`.
  have hcard : ∀ t : ℕ, ((W.filter (fun w => wcSup w ≤ t)).card : ℝ)
      = ∑ w ∈ W, (if wcSup w ≤ t then (1 : ℝ) else 0) := by
    intro t
    exact (Finset.sum_boole (fun w => wcSup w ≤ t) W).symm
  -- The contribution of a single `w` is the telescoped tail sum.
  have hper : ∀ w ∈ W, (∑ t ∈ Finset.Icc 1 r,
        (if wcSup w ≤ t then (1 : ℝ) else 0) / ((t : ℝ) * ((t : ℝ) + 1)))
      = 1 / (wcSup w : ℝ) - 1 / ((r : ℝ) + 1) := by
    intro w hw
    have hm1 : 1 ≤ wcSup w := wcSup_pos_of_ne_zero (hne w hw)
    have hmr : wcSup w ≤ r := hbox w hw
    have hfilt : (Finset.Icc 1 r).filter (fun t => wcSup w ≤ t) = Finset.Icc (wcSup w) r := by
      ext t; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    simp only [ite_div, zero_div]
    rw [← Finset.sum_filter]
    rw [hfilt]
    exact wc_sum_inv_sup_telescope (wcSup w) r hm1 hmr
  -- Expand, exchange the two finite sums, and telescope termwise.
  have hmain : ∑ t ∈ Finset.Icc 1 r,
        ((W.filter (fun w => wcSup w ≤ t)).card : ℝ) / ((t : ℝ) * ((t : ℝ) + 1))
      = ∑ w ∈ W, 1 / (wcSup w : ℝ) - (W.card : ℝ) / ((r : ℝ) + 1) := by
    calc
      ∑ t ∈ Finset.Icc 1 r,
          ((W.filter (fun w => wcSup w ≤ t)).card : ℝ) / ((t : ℝ) * ((t : ℝ) + 1))
        = ∑ t ∈ Finset.Icc 1 r,
            (∑ w ∈ W, (if wcSup w ≤ t then (1 : ℝ) else 0))
              / ((t : ℝ) * ((t : ℝ) + 1)) := by
            apply Finset.sum_congr rfl; intro t _; rw [hcard t]
      _ = ∑ t ∈ Finset.Icc 1 r, ∑ w ∈ W,
            (if wcSup w ≤ t then (1 : ℝ) else 0) / ((t : ℝ) * ((t : ℝ) + 1)) := by
            apply Finset.sum_congr rfl; intro t _; rw [Finset.sum_div]
      _ = ∑ w ∈ W, ∑ t ∈ Finset.Icc 1 r,
            (if wcSup w ≤ t then (1 : ℝ) else 0) / ((t : ℝ) * ((t : ℝ) + 1)) := by
            rw [Finset.sum_comm]
      _ = ∑ w ∈ W, (1 / (wcSup w : ℝ) - 1 / ((r : ℝ) + 1)) := by
            apply Finset.sum_congr rfl; intro w hw; exact hper w hw
      _ = ∑ w ∈ W, 1 / (wcSup w : ℝ) - (W.card : ℝ) / ((r : ℝ) + 1) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, one_div,
              div_eq_mul_inv]
  rw [hmain]
  ring

end Work.FIArea2.R6
