import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.Calculus

/-- Norm bound for the derivative of the Newtonian force kernel. -/
theorem norm_inv_cube_norm_smul_deriv_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (u u' : F) :
    ‖((‖u‖ ^ 3)⁻¹) • u' - (3 * ((‖u‖ ^ 5)⁻¹ * inner ℝ u u')) • u‖
      ≤ 4 * ‖u'‖ * (‖u‖ ^ 3)⁻¹ := by
  rcases eq_or_ne ‖u‖ 0 with h0 | hne
  · have hu0 : u = 0 := norm_eq_zero.mp h0
    rw [h0, hu0]
    simp
  · have hnn5 : (0:ℝ) ≤ (‖u‖ ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (norm_nonneg u) 5)
    have hnn3 : (0:ℝ) ≤ (‖u‖ ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg (norm_nonneg u) 3)
    have hu : (0:ℝ) ≤ ‖u‖ := norm_nonneg u
    have hinn : |inner ℝ u u'| ≤ ‖u‖ * ‖u'‖ := by
      simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) u u'
    have e1 : ‖((‖u‖ ^ 3)⁻¹) • u'‖ = (‖u‖ ^ 3)⁻¹ * ‖u'‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnn3]
    have e2 : ‖(3 * ((‖u‖ ^ 5)⁻¹ * inner ℝ u u')) • u‖
        ≤ 3 * (‖u‖ ^ 5)⁻¹ * (‖u‖ * ‖u'‖) * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (show (0:ℝ) ≤ 3 by norm_num), abs_of_nonneg hnn5]
      calc 3 * ((‖u‖ ^ 5)⁻¹ * |inner ℝ u u'|) * ‖u‖
          = 3 * (((‖u‖ ^ 5)⁻¹ * |inner ℝ u u'|) * ‖u‖) := by ring
        _ ≤ 3 * (((‖u‖ ^ 5)⁻¹ * (‖u‖ * ‖u'‖)) * ‖u‖) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinn hnn5) hu)
                (by norm_num)
        _ = 3 * (‖u‖ ^ 5)⁻¹ * (‖u‖ * ‖u'‖) * ‖u‖ := by ring
    have e3 : (‖u‖ ^ 3)⁻¹ * ‖u'‖ + 3 * (‖u‖ ^ 5)⁻¹ * (‖u‖ * ‖u'‖) * ‖u‖
        = 4 * ‖u'‖ * (‖u‖ ^ 3)⁻¹ := by
      have hrr : (‖u‖ ^ 5)⁻¹ * ‖u‖ ^ 2 = (‖u‖ ^ 3)⁻¹ := by
        field_simp
      have h4 : 3 * (‖u‖ ^ 5)⁻¹ * (‖u‖ * ‖u'‖) * ‖u‖ = 3 * ‖u'‖ * (‖u‖ ^ 3)⁻¹ := by
        rw [← hrr]; ring
      rw [h4]; ring
    calc ‖((‖u‖ ^ 3)⁻¹) • u' - (3 * ((‖u‖ ^ 5)⁻¹ * inner ℝ u u')) • u‖
        ≤ ‖((‖u‖ ^ 3)⁻¹) • u'‖ + ‖(3 * ((‖u‖ ^ 5)⁻¹ * inner ℝ u u')) • u‖ :=
            norm_sub_le _ _
      _ = (‖u‖ ^ 3)⁻¹ * ‖u'‖ + ‖(3 * ((‖u‖ ^ 5)⁻¹ * inner ℝ u u')) • u‖ := by rw [e1]
      _ ≤ (‖u‖ ^ 3)⁻¹ * ‖u'‖ + 3 * (‖u‖ ^ 5)⁻¹ * (‖u‖ * ‖u'‖) * ‖u‖ :=
            add_le_add le_rfl e2
      _ = 4 * ‖u'‖ * (‖u‖ ^ 3)⁻¹ := e3

end Commons.Analysis.Calculus