import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs

namespace Work.ZeroDensity.Ingham

/-- Each summand of `M_K(1) = Σ_{n ≤ K} μ(n) n^{-1}` is bounded by `1/n` in norm. -/
private lemma norm_moebius_mul_cpow_neg_one_le (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(1 : ℂ))‖ ≤ (n : ℝ)⁻¹ := by
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    by_cases h : Squarefree n
    · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
      norm_num
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
      norm_num
  rw [norm_mul, Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
  have h1 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * (n : ℝ)⁻¹ ≤ 1 * (n : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hmu h1
    _ = (n : ℝ)⁻¹ := one_mul _

/-- The harmonic sum bound in the shape needed here. -/
private lemma sum_Icc_one_div_le (K : ℕ) :
    (∑ n ∈ Finset.Icc 1 K, (n : ℝ)⁻¹) ≤ 1 + Real.log (K : ℝ) := by
  have hhar : (harmonic K : ℝ) = ∑ n ∈ Finset.Icc 1 K, (n : ℝ)⁻¹ := by
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← hhar]
  exact harmonic_le_one_add_log K

lemma mkOneNormBound (K : ℕ) : ‖MK K 1‖ ≤ 1 + Real.log (K : ℝ) := by
  rw [MK_apply]
  calc ‖∑ n ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(1 : ℂ))‖
      ≤ ∑ n ∈ Finset.Icc 1 K, ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(1 : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 K, (n : ℝ)⁻¹ :=
        Finset.sum_le_sum fun n _ => norm_moebius_mul_cpow_neg_one_le n
    _ ≤ 1 + Real.log (K : ℝ) := sum_Icc_one_div_le K

end Work.ZeroDensity.Ingham
