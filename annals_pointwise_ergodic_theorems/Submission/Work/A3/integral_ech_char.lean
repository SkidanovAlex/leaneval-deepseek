import Mathlib

namespace Work.A3

/-- Orthogonality of the characters `θ ↦ e(-Mθ)` on the unit interval:
`∫₀¹ exp(-2πiMθ) dθ` is `1` if `M = 0` and `0` otherwise. -/
theorem integral_ech_char (M : ℤ) :
    ∫ θ in Set.Icc (0:ℝ) 1, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (M : ℂ)) * θ) = if M = 0 then (1 : ℂ) else 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  rcases eq_or_ne M 0 with hM | hM
  · subst hM; simp
  · rw [if_neg hM]
    rw [integral_exp_mul_complex (a := 0) (b := 1) (by
      rw [neg_ne_zero]
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero)
        (Int.cast_ne_zero.mpr hM))]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (M : ℂ) = (M : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
    rw [Complex.exp_neg, Complex.exp_int_mul_two_pi_mul_I, inv_one]
    ring

end Work.A3
