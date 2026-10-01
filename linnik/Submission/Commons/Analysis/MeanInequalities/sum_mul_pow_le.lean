import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.BigOperators.Field

namespace Commons.Analysis.MeanInequalities

open Finset

/-- Weighted Hölder inequality in power form: for nonnegative `A`, `M` and `k ≥ 1`,
`(∑ A_i M_i)^k ≤ (∑ A_i)^(k-1) * ∑ A_i M_i^k`. -/
theorem sum_mul_pow_le {ι : Type*} (s : Finset ι) (A M : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hM : ∀ i ∈ s, 0 ≤ M i)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ s, A i * M i) ^ k ≤ (∑ i ∈ s, A i) ^ (k - 1) * ∑ i ∈ s, A i * (M i) ^ k := by
  by_cases hW : ∑ i ∈ s, A i = 0
  · have hA0 : ∀ i ∈ s, A i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hA).mp hW
    have hS : ∑ i ∈ s, A i * M i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hA0 i hi, zero_mul]
    have hT : ∑ i ∈ s, A i * (M i) ^ k = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hA0 i hi, zero_mul]
    have hk0 : k ≠ 0 := by omega
    rw [hS, hT, zero_pow hk0]
    simp
  · have hWpos : 0 < ∑ i ∈ s, A i :=
      lt_of_le_of_ne (Finset.sum_nonneg hA) (Ne.symm hW)
    have hJ := Real.pow_arith_mean_le_arith_mean_pow s
      (fun i => A i / ∑ j ∈ s, A j) M
      (fun i hi => div_nonneg (hA i hi) hWpos.le)
      (by rw [← Finset.sum_div]; exact div_self hW)
      (fun i hi => hM i hi) k
    have hS : ∑ i ∈ s, A i / (∑ j ∈ s, A j) * M i = (∑ i ∈ s, A i * M i) / (∑ j ∈ s, A j) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => div_mul_eq_mul_div _ _ _
    have hT : ∑ i ∈ s, A i / (∑ j ∈ s, A j) * (M i) ^ k
        = (∑ i ∈ s, A i * (M i) ^ k) / (∑ j ∈ s, A j) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => div_mul_eq_mul_div _ _ _
    rw [hS, hT, div_pow] at hJ
    have hpow : (∑ j ∈ s, A j) ^ (k - 1) = (∑ j ∈ s, A j) ^ k * (∑ j ∈ s, A j)⁻¹ := by
      simpa using pow_sub₀ (∑ j ∈ s, A j) hW hk
    have hWk : (0:ℝ) < (∑ i ∈ s, A i) ^ k := pow_pos hWpos k
    have hWkne : (∑ i ∈ s, A i) ^ k ≠ 0 := ne_of_gt hWk
    have hkey := mul_le_mul_of_nonneg_right hJ hWk.le
    rw [div_mul_cancel₀ _ hWkne] at hkey
    have hrhs : ((∑ i ∈ s, A i * (M i) ^ k) / (∑ j ∈ s, A j)) * (∑ j ∈ s, A j) ^ k
        = (∑ j ∈ s, A j) ^ (k - 1) * ∑ i ∈ s, A i * (M i) ^ k := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_eq_mul_inv, ← hpow]
      ring
    rw [hrhs] at hkey
    exact hkey

end Commons.Analysis.MeanInequalities
