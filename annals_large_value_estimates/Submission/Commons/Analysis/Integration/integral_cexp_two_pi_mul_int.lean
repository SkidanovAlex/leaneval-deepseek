import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.Analysis.Integration

theorem integral_cexp_two_pi_mul_int (k : ℤ) :
    (∫ α in (0 : ℝ)..1, Complex.exp (↑(2 * Real.pi * α * (k : ℝ)) * Complex.I))
      = if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    simp
  · rw [if_neg hk]
    set c : ℂ := ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I with hc_def
    have hc : c ≠ 0 := by
      rw [hc_def]
      apply mul_ne_zero
      · rw [Complex.ofReal_ne_zero]
        exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by exact_mod_cast hk)
      · exact Complex.I_ne_zero
    have h_int : (∫ α in (0 : ℝ)..1, Complex.exp (↑(2 * Real.pi * α * (k : ℝ)) * Complex.I))
        = ∫ α in (0 : ℝ)..1, Complex.exp (c * (α : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro α _
      rw [hc_def]
      push_cast
      ring_nf
    rw [h_int, integral_exp_mul_complex hc]
    have hc1 : c * (1 : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hc_def]; push_cast; ring_nf
    simp only [Complex.ofReal_one, Complex.ofReal_zero, hc1, mul_zero, Complex.exp_zero,
      Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div]

end Commons.Analysis.Integration