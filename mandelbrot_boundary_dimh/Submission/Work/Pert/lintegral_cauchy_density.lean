import Mathlib

namespace Work.Pert

/-- The total mass of the Cauchy density `y ↦ (a ^ 2 + y ^ 2)⁻¹` is `π / |a|`. -/
theorem integral_inv_sq_add_sq {a : ℝ} (ha0 : a ≠ 0) :
    ∫ y : ℝ, (a ^ 2 + y ^ 2)⁻¹ = Real.pi / |a| := by
  have hb : (1 / a : ℝ) ≠ 0 := by simp [ha0]
  have hfun : (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹)
      = fun y => (a ^ 2)⁻¹ * (1 + ((1 / a) * y) ^ 2)⁻¹ := by
    funext y; field_simp
  rw [hfun, MeasureTheory.integral_const_mul, integral_univ_inv_one_add_mul_sq (1 / a)]
  have h1 : |((1 : ℝ) / a)| = |a|⁻¹ := by rw [one_div, abs_inv]
  rw [h1, div_inv_eq_mul, ← sq_abs a]
  field_simp

theorem lintegral_cauchy_density {a : ℝ} (ha : 64 * Real.pi ≤ |a|) :
    ∫⁻ y : ℝ, ENNReal.ofReal ((a ^ 2 + y ^ 2)⁻¹) ≤ ENNReal.ofReal (1 / 64) := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, abs_zero] at ha
    have : (0 : ℝ) < 64 * Real.pi := by positivity
    linarith
  have hb : (1 / a : ℝ) ≠ 0 := by simp [ha0]
  have hfun : (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹)
      = fun y => (a ^ 2)⁻¹ * (1 + ((1 / a) * y) ^ 2)⁻¹ := by
    funext y; field_simp
  have hint : MeasureTheory.Integrable (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) := by
    rw [hfun]
    exact (integrable_inv_one_add_mul_sq hb).const_mul _
  have hnn : 0 ≤ᵐ[MeasureTheory.volume] (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) :=
    Filter.Eventually.of_forall fun y => by positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn,
    integral_inv_sq_add_sq ha0]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (abs_pos.mpr ha0)]
  nlinarith [ha]

end Work.Pert
