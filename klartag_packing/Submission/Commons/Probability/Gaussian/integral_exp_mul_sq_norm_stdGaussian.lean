import Mathlib
import Submission.Commons.Probability.Gaussian.integral_exp_mul_sq_gaussianReal

namespace Commons.Probability.Gaussian

open MeasureTheory ProbabilityTheory

/-- The (Laplace) transform of the standard Gaussian measure on `EuclideanSpace ℝ (Fin n)`:
for `t < 1/2`,
`∫ exp (t * ‖x‖²) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = (√(1 - 2 t))⁻¹ ^ n`.
This is the `n`-fold product of the one-dimensional formula
`Commons.Probability.Gaussian.integral_exp_mul_sq_gaussianReal`. -/
theorem integral_exp_mul_sq_norm_stdGaussian {n : ℕ} {t : ℝ} (ht : t < 1 / 2) :
    ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (t * ‖x‖ ^ 2)
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)))
      = ((Real.sqrt (1 - 2 * t))⁻¹) ^ n := by
  -- `stdGaussian` on `EuclideanSpace ℝ (Fin n)` is the pushforward of the product of `n`
  -- one-dimensional standard Gaussians under `toLp 2`.
  rw [← map_pi_eq_stdGaussian]
  rw [integral_map (by fun_prop) (by fun_prop)]
  -- `‖toLp 2 y‖² = ∑ i, (y i)²`, so the exponential splits as a product.
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  have hprod : ∀ y : Fin n → ℝ, Real.exp (t * ∑ i, (y i) ^ 2)
      = ∏ i, Real.exp (t * (y i) ^ 2) := by
    intro y
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hprod]
  -- Fubini for finitely many variables, then the one-dimensional Laplace transform.
  rw [integral_fintype_prod_eq_pow (f := fun a : ℝ => Real.exp (t * a ^ 2))]
  rw [Commons.Probability.Gaussian.integral_exp_mul_sq_gaussianReal ht, Fintype.card_fin]

end Commons.Probability.Gaussian
