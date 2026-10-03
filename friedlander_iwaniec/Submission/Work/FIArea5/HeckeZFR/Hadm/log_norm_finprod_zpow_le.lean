import Mathlib
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset

namespace Work.FIArea5.HeckeZFR.Hadm

theorem log_norm_finprod_zpow_le {d : ℂ → ℤ} (hsupp : (Function.support d).Finite)
    (hdn : ∀ u : ℂ, 0 ≤ d u) {z : ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hz : ∀ u : ℂ, d u ≠ 0 → z ≠ u)
    (hB : ∀ u : ℂ, d u ≠ 0 → Real.log ‖z - u‖ ≤ B) :
    Real.log ‖∏ᶠ u : ℂ, (z - u) ^ (d u)‖ ≤ (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * B := by
  classical
  have hmem : ∀ u : ℂ, u ∈ hsupp.toFinset ↔ d u ≠ 0 := by
    intro u; rw [hsupp.mem_toFinset, Function.mem_support]
  have hmul : Function.mulSupport (fun u : ℂ => (z - u) ^ (d u)) ⊆ Function.support d := by
    intro u hu
    rw [Function.mem_support]
    intro hdu
    rw [Function.mem_mulSupport] at hu
    exact hu (by simp [hdu])
  have hfne : ∀ u : ℂ, u ∈ hsupp.toFinset → (z - u) ^ (d u) ≠ 0 := by
    intro u hu
    have hdu : d u ≠ 0 := (hmem u).mp hu
    exact zpow_ne_zero _ (sub_ne_zero.mpr (hz u hdu))
  have hnorm_ne : ∀ u : ℂ, u ∈ hsupp.toFinset → ‖(z - u) ^ (d u)‖ ≠ 0 :=
    fun u hu => norm_ne_zero_iff.mpr (hfne u hu)
  have hsum : Function.support (fun u : ℂ => ((d u : ℤ) : ℝ)) ⊆ Function.support d := by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hdu
    exact hu (by simp [hdu])
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite (fun u : ℂ => (z - u) ^ (d u)) hmul hsupp,
      norm_prod, Real.log_prod hnorm_ne]
  simp only [Complex.norm_zpow, Real.log_zpow]
  rw [finsum_eq_sum_of_support_subset_of_finite (fun u : ℂ => ((d u : ℤ) : ℝ)) hsum hsupp]
  calc ∑ u ∈ hsupp.toFinset, ((d u : ℤ) : ℝ) * Real.log ‖z - u‖
      ≤ ∑ u ∈ hsupp.toFinset, ((d u : ℤ) : ℝ) * B := by
        apply Finset.sum_le_sum
        intro u hu
        exact mul_le_mul_of_nonneg_left (hB u ((hmem u).mp hu)) (Int.cast_nonneg (hdn u))
    _ = (∑ u ∈ hsupp.toFinset, ((d u : ℤ) : ℝ)) * B := by rw [Finset.sum_mul]

end Work.FIArea5.HeckeZFR.Hadm
