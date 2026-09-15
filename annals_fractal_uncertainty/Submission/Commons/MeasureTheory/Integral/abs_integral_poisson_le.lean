import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.MeasureTheory.Integral

open _root_.MeasureTheory _root_.Real _root_.Set _root_.Filter
open scoped ENNReal

/-- **The Poisson integral is a sup-norm contraction.**  Since the Poisson kernel
`u ↦ y/(π(y²+u²))` is nonnegative with integral `1` on `ℝ` (for `y > 0`), the Poisson extension
`(P_y f)(x) = ∫ f(u) y/(π(y²+u²)) du` of a bounded function is bounded by the same constant. -/
theorem abs_integral_poisson_le (f : ℝ → ℝ) {C y : ℝ} (hy : 0 < y) (hf : ∀ u, |f u| ≤ C) :
    |∫ u : ℝ, f u * (y / (Real.pi * (y ^ 2 + u ^ 2)))| ≤ C := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hKnn : ∀ u : ℝ, 0 ≤ y / (Real.pi * (y ^ 2 + u ^ 2)) := by
    intro u
    apply div_nonneg hy.le
    exact mul_nonneg Real.pi_pos.le (by positivity)
  have hpoint : ∀ u : ℝ,
      y / (Real.pi * (y ^ 2 + u ^ 2)) = (Real.pi * y)⁻¹ * (1 + (u / y) ^ 2)⁻¹ := by
    intro u
    have hden : y ^ 2 + u ^ 2 ≠ 0 := by positivity
    field_simp
  have hg : ∫ u : ℝ, (1 + (u / y) ^ 2)⁻¹ = y * Real.pi := by
    have h := Measure.integral_comp_div (fun v : ℝ => (1 + v ^ 2)⁻¹) y
    rw [integral_univ_inv_one_add_sq, abs_of_pos hy, smul_eq_mul] at h
    exact h
  have hKint : ∫ u : ℝ, y / (Real.pi * (y ^ 2 + u ^ 2)) = 1 := by
    simp_rw [hpoint]
    rw [integral_const_mul, hg]
    rw [mul_comm y Real.pi, inv_mul_cancel₀ (mul_ne_zero hpi hy0)]
  have hKintble : Integrable (fun u : ℝ => y / (Real.pi * (y ^ 2 + u ^ 2))) := by
    have hbase : Integrable (fun v : ℝ => (1 + v ^ 2)⁻¹) := integrable_inv_one_add_sq
    have hcomp : Integrable (fun u : ℝ => (1 + (u / y) ^ 2)⁻¹) := hbase.comp_div hy0
    have heq : (fun u : ℝ => y / (Real.pi * (y ^ 2 + u ^ 2)))
        = fun u : ℝ => (Real.pi * y)⁻¹ * (1 + (u / y) ^ 2)⁻¹ := by
      funext u; exact hpoint u
    rw [heq]; exact hcomp.const_mul _
  have hCK : Integrable (fun u : ℝ => C * (y / (Real.pi * (y ^ 2 + u ^ 2)))) :=
    hKintble.const_mul C
  have hbound : ∀ u : ℝ,
      ‖f u * (y / (Real.pi * (y ^ 2 + u ^ 2)))‖ ≤ C * (y / (Real.pi * (y ^ 2 + u ^ 2))) := by
    intro u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hKnn u)]
    exact mul_le_mul_of_nonneg_right (hf u) (hKnn u)
  have hmain := norm_integral_le_of_norm_le hCK (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at hmain
  calc |∫ u : ℝ, f u * (y / (Real.pi * (y ^ 2 + u ^ 2)))|
      ≤ ∫ u : ℝ, C * (y / (Real.pi * (y ^ 2 + u ^ 2))) := hmain
    _ = C * ∫ u : ℝ, y / (Real.pi * (y ^ 2 + u ^ 2)) := integral_const_mul C _
    _ = C * 1 := by rw [hKint]
    _ = C := mul_one C

end Commons.MeasureTheory.Integral