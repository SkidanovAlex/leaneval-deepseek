import Mathlib

namespace Work.Pert

/-- For `κ > 0` and `0 ≤ Y`, the integral of `exp(-(κ t))` over `[Y, y]` is at most `1/κ`,
independently of `y`. -/
theorem integral_exp_neg_mul_le {κ Y y : ℝ} (hκ : 0 < κ) (hY : 0 ≤ Y) (hYy : Y ≤ y) :
    ∫ t in Y..y, Real.exp (-(κ * t)) ≤ 1 / κ := by
  have _ := hYy
  -- Change variables `u = -κ t` and evaluate the resulting exponential integral.
  have hcomp : ∫ t in Y..y, Real.exp ((-κ) * t)
      = (-κ)⁻¹ * ∫ u in (-κ) * Y..(-κ) * y, Real.exp u := by
    rw [intervalIntegral.integral_comp_mul_left (f := Real.exp) (c := -κ) (by linarith)]
    simp
  rw [show ∫ t in Y..y, Real.exp (-(κ * t)) = ∫ t in Y..y, Real.exp ((-κ) * t) by
        simp [mul_comm]]
  rw [hcomp, integral_exp]
  have hval : (-κ)⁻¹ * (Real.exp ((-κ) * y) - Real.exp ((-κ) * Y))
      = (Real.exp ((-κ) * Y) - Real.exp ((-κ) * y)) / κ := by
    field_simp
    ring
  rw [hval, div_le_div_iff_of_pos_right hκ]
  have hexpY : Real.exp ((-κ) * Y) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [hY, hκ])
  have hy : 0 ≤ Real.exp ((-κ) * y) := Real.exp_nonneg _
  linarith

end Work.Pert
