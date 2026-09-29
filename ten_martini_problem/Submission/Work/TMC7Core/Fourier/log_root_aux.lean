import Mathlib

/-!
# Auxiliary lemmas for `log_root_fourier`

Basic ingredients for the Fourier coefficient of `x ↦ log ‖e^{2πix} - α‖`:

* `integral_exp_two_pi_I_int` : `∫₀¹ exp (2πi m x) dx` for `m : ℤ`;
* `log_one_sub_mul_exp_hasSum` : the Taylor series of `log (1 - z e^{2πix})`.
-/

namespace Work.TMC7Core.Fourier

/-- `∫₀¹ exp (2 * π * I * m * x) dx = 1` if `m = 0` and `0` otherwise. -/
lemma integral_exp_two_pi_I_int (m : ℤ) :
    ∫ x in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (m : ℝ) * x)
      = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm]
    have hc : (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      have hp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      exact mul_ne_zero hm0 hp
    rw [show (∫ x in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (m : ℝ) * x))
          = ∫ x in (0 : ℝ)..1,
              Complex.exp (((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (x : ℂ)) by
        apply intervalIntegral.integral_congr; intro x _
        push_cast; ring_nf]
    rw [integral_exp_mul_complex hc]
    rw [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero,
        Complex.exp_int_mul_two_pi_mul_I m, Complex.exp_zero, sub_self, zero_div]

/-- The Taylor series of `log (1 - z * exp (2πi x))`, valid for `‖z‖ < 1`. -/
lemma log_one_sub_mul_exp_hasSum (z : ℂ) (hz : ‖z‖ < 1) (x : ℝ) :
    HasSum (fun n : ℕ => -(z ^ n / n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x))
      (Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x))) := by
  have hE : ‖Complex.exp (2 * Real.pi * Complex.I * x)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hzw : ‖z * Complex.exp (2 * Real.pi * Complex.I * x)‖ < 1 := by
    rw [Complex.norm_mul, hE, mul_one]; exact hz
  have hw := (Complex.hasSum_taylorSeries_neg_log hzw).neg
  have key : ∀ n : ℕ, -(z ^ n / n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x)
      = -((z * Complex.exp (2 * Real.pi * Complex.I * x)) ^ n / n) := by
    intro n
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have := hw.congr_fun key
  simpa using this

end Work.TMC7Core.Fourier
