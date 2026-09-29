import Mathlib
import Submission.Work.Fx.scaleCommon

namespace Work.Fx

/-- Triangle-inequality scaling lemma (paper Lemma 2.2, the "‖·‖ does not grow the
error by more than the scale factor" step): the disc coordinate magnitude of the
scaled pair `(c·x₀, c·y₀)` is at most `2^p · c · ‖x‖` plus the scaled image error.

Write `a = x₀ + y₀·I` and `b = 2^p · x`.  Then
`√((c·x₀)² + (c·y₀)²) = c·‖a‖ ≤ c·(‖a - b‖ + ‖b‖) = c·‖a - b‖ + 2^p·c·‖x‖`
by the triangle inequality `a = (a - b) + b`. -/
theorem scale_sqrt_le (p c : ℕ) (x0 y0 : ℤ) (x : ℂ) :
    Real.sqrt (((((c : ℤ) * x0 : ℤ)) : ℝ) ^ 2 + ((((c : ℤ) * y0 : ℤ)) : ℝ) ^ 2)
      ≤ (2 : ℝ) ^ p * (c : ℝ) * ‖x‖
        + (c : ℝ) * ‖(x0 : ℂ) + (y0 : ℂ) * Complex.I - ((2 : ℝ) ^ p : ℂ) * x‖ := by
  set a : ℂ := (x0 : ℂ) + (y0 : ℂ) * Complex.I with ha
  set b : ℂ := ((2 : ℝ) ^ p : ℂ) * x with hb
  -- `‖a‖` is the square root of the sum of squares of the integer coordinates
  have ha' : a = ((x0 : ℝ) : ℂ) + ((y0 : ℝ) : ℂ) * Complex.I := by
    rw [ha]; push_cast; ring
  have hsq : ‖a‖ ^ 2 = (x0 : ℝ) ^ 2 + (y0 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ha', Complex.normSq_add_mul_I]
  have hnorm : ‖a‖ = Real.sqrt ((x0 : ℝ) ^ 2 + (y0 : ℝ) ^ 2) := by
    rw [← hsq]
    exact (Real.sqrt_sq (norm_nonneg a)).symm
  -- the left-hand side is `c · ‖a‖`
  have hL : Real.sqrt (((((c : ℤ) * x0 : ℤ)) : ℝ) ^ 2 + ((((c : ℤ) * y0 : ℤ)) : ℝ) ^ 2)
      = (c : ℝ) * ‖a‖ := by
    rw [hnorm]
    have hX : ((((c : ℤ) * x0 : ℤ)) : ℝ) ^ 2 + ((((c : ℤ) * y0 : ℤ)) : ℝ) ^ 2
        = (c : ℝ) ^ 2 * ((x0 : ℝ) ^ 2 + (y0 : ℝ) ^ 2) := by push_cast; ring
    rw [hX, Real.sqrt_mul (sq_nonneg (c : ℝ)), Real.sqrt_sq (Nat.cast_nonneg c)]
  -- triangle inequality with `a = (a - b) + b`
  have h2 : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
  have h3 : ‖b‖ = (2 : ℝ) ^ p * ‖x‖ := by
    rw [hb, norm_mul]
    simp
  rw [hL]
  calc (c : ℝ) * ‖a‖
      ≤ (c : ℝ) * (‖a - b‖ + ‖b‖) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg c)
    _ = (2 : ℝ) ^ p * (c : ℝ) * ‖x‖ + (c : ℝ) * ‖a - b‖ := by rw [h3]; ring

end Work.Fx
