/-
# Minkowski's inequality in `ℓ^r` for `ENNReal`-valued families

The finite `ℓ^r` Minkowski inequality for families of nonnegative (extended) real numbers,
`(∑_{j ∈ s} (∑_{i ∈ t} x i j)^r)^{1/r} ≤ ∑_{i ∈ t} (∑_{j ∈ s} (x i j)^r)^{1/r}`, together with
the subadditivity of `t ↦ t^{1/r}`.  These are the tools that let the Rademacher--Menshov
arguments split a sum over dyadic scales.
-/
import Mathlib

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Variation

/-- The two-term `ℓ^r` Minkowski inequality for `ENNReal`-valued families: this is
`ENNReal.Lp_add_le` (`Mathlib.Analysis.MeanInequalities`). -/
theorem add_rpow_sum_le {r : ℝ} (hr : 1 ≤ r) {ι : Type*} (s : Finset ι) (a b : ι → ENNReal) :
    (∑ j ∈ s, (a j + b j) ^ r) ^ (1 / r)
      ≤ (∑ j ∈ s, a j ^ r) ^ (1 / r) + (∑ j ∈ s, b j ^ r) ^ (1 / r) :=
  ENNReal.Lp_add_le s a b hr

/-- **Minkowski's inequality in `ℓ^r`, finite form, for `ENNReal`-valued families.** -/
theorem rpow_sum_sum_le {r : ℝ} (hr : 1 ≤ r) {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (x : κ → ι → ENNReal) :
    (∑ j ∈ s, (∑ i ∈ t, x i j) ^ r) ^ (1 / r)
      ≤ ∑ i ∈ t, (∑ j ∈ s, (x i j) ^ r) ^ (1 / r) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have hr0 : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hr
      simp only [Finset.sum_empty, ENNReal.zero_rpow_of_pos hr0, Finset.sum_const_zero,
        ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1 / r)]
      simp
  | insert a t ha ih =>
      calc (∑ j ∈ s, (∑ i ∈ insert a t, x i j) ^ r) ^ (1 / r)
          = (∑ j ∈ s, (x a j + ∑ i ∈ t, x i j) ^ r) ^ (1 / r) := by
            simp [Finset.sum_insert ha]
        _ ≤ (∑ j ∈ s, (x a j) ^ r) ^ (1 / r) + (∑ j ∈ s, (∑ i ∈ t, x i j) ^ r) ^ (1 / r) :=
            add_rpow_sum_le hr s (fun j => x a j) (fun j => ∑ i ∈ t, x i j)
        _ ≤ (∑ j ∈ s, (x a j) ^ r) ^ (1 / r)
              + ∑ i ∈ t, (∑ j ∈ s, (x i j) ^ r) ^ (1 / r) := add_le_add le_rfl ih
        _ = ∑ i ∈ insert a t, (∑ j ∈ s, (x i j) ^ r) ^ (1 / r) := by
            rw [Finset.sum_insert ha]

/-- Subadditivity of the `(1/r)`-th root on `ENNReal` for `r ≥ 1`. -/
theorem rpow_sum_le_sum_rpow {r : ℝ} (hr : 1 ≤ r) {ι : Type*} (s : Finset ι) (x : ι → ENNReal) :
    (∑ i ∈ s, x i) ^ (1 / r) ≤ ∑ i ∈ s, x i ^ (1 / r) := by
  classical
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hle : 1 / r ≤ 1 := by
    simpa using one_div_le_one_div_of_le (show (0:ℝ) < 1 by norm_num) (by simpa using hr)
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1 / r)]
      simp
  | insert a s ha ih =>
      calc (∑ i ∈ insert a s, x i) ^ (1 / r)
          = (x a + ∑ i ∈ s, x i) ^ (1 / r) := by rw [Finset.sum_insert ha]
        _ ≤ (x a) ^ (1 / r) + (∑ i ∈ s, x i) ^ (1 / r) :=
            ENNReal.rpow_add_le_add_rpow _ _ (by positivity) hle
        _ ≤ (x a) ^ (1 / r) + ∑ i ∈ s, x i ^ (1 / r) := add_le_add le_rfl ih
        _ = ∑ i ∈ insert a s, x i ^ (1 / r) := by rw [Finset.sum_insert ha]

end Work.Analysis.Variation
