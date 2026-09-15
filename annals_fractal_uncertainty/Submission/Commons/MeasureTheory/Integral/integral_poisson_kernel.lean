import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Real Set Filter
open scoped ENNReal

namespace Commons.MeasureTheory.Integral

/-- The Poisson kernel `u ↦ y / (π(y² + u²))` has integral `1` on `ℝ` (for `y > 0`).
Substituting `u = y v` reduces it to `π⁻¹ ∫_ℝ dv/(1 + v²) = 1`. -/
theorem integral_poisson_kernel {y : ℝ} (hy : 0 < y) :
    ∫ u : ℝ, y / (Real.pi * (y ^ 2 + u ^ 2)) = 1 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  -- Step 1: pointwise rewrite in terms of the rescaled integrand.
  have hpt : ∀ u : ℝ, y / (Real.pi * (y ^ 2 + u ^ 2))
      = (Real.pi)⁻¹ * y⁻¹ * (1 + (u / y) ^ 2)⁻¹ := by
    intro u
    have hy2 : y ^ 2 + u ^ 2 ≠ 0 := by positivity
    field_simp
  -- Step 2: pull out the constant factor and change variables u = y v.
  have hg : ∫ u : ℝ, (1 + (u / y) ^ 2)⁻¹ = y * Real.pi := by
    have h := Measure.integral_comp_div (fun v : ℝ => (1 + v ^ 2)⁻¹) y
    rw [abs_of_pos hy, integral_univ_inv_one_add_sq, smul_eq_mul] at h
    exact h
  calc ∫ u : ℝ, y / (Real.pi * (y ^ 2 + u ^ 2))
      = ∫ u : ℝ, (Real.pi)⁻¹ * y⁻¹ * (1 + (u / y) ^ 2)⁻¹ := by
        apply integral_congr_ae; filter_upwards with u; exact hpt u
    _ = (Real.pi)⁻¹ * y⁻¹ * ∫ u : ℝ, (1 + (u / y) ^ 2)⁻¹ := by
        rw [integral_const_mul]
    _ = (Real.pi)⁻¹ * y⁻¹ * (y * Real.pi) := by rw [hg]
    _ = 1 := by field_simp

end Commons.MeasureTheory.Integral