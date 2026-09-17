import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.integral_gaussianReal_zero_one

namespace Commons.Probability.Gaussian

open MeasureTheory

/-- The Laplace-transform (moment generating function) of the standard Gaussian: for `t < 1/2`,
`∫ exp (t x ^ 2) ∂(gaussianReal 0 1) = (√(1 - 2 t))⁻¹`.  Equivalently, if `Z` is a standard
normal random variable then `E[exp (t Z ^ 2)] = (1 - 2 t) ^ (-1/2)`. -/
theorem integral_exp_mul_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    ∫ x : ℝ, Real.exp (t * x ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1)
      = (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hs : (0:ℝ) < 1 - 2 * t := by linarith
  rw [Commons.Analysis.GaussianMeasure.integral_gaussianReal_zero_one]
  -- combine the two exponentials: `exp (t x²) * exp (-x²/2) = exp (-(1/2 - t) x²)`
  have hint : ∀ x : ℝ, Real.exp (t * x ^ 2) * Real.exp (-(x ^ 2 / 2))
      = Real.exp (-(1 / 2 - t) * x ^ 2) := by
    intro x
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hint]
  -- evaluate the resulting Gaussian integral
  rw [integral_gaussian (1 / 2 - t)]
  have hp : Real.pi / (1 / 2 - t) = (2 * Real.pi) / (1 - 2 * t) := by
    field_simp
  rw [hp, Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 * Real.pi) (1 - 2 * t)]
  rw [div_eq_mul_inv, ← mul_assoc,
    inv_mul_cancel₀ (by positivity : Real.sqrt (2 * Real.pi) ≠ 0)]
  simp

end Commons.Probability.Gaussian
