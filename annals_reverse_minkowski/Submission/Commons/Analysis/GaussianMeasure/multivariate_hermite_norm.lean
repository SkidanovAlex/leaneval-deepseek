import Mathlib.MeasureTheory.Integral.Pi
import Submission.Commons.Analysis.GaussianMeasure.hermite_gaussian_norm

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Polynomial
open scoped BigOperators

noncomputable section

/-- For `x : EuclideanSpace ℝ (Fin m)`, the squared norm is the sum of the squares of
the coordinates. -/
private lemma norm_sq_eq_sum_sq {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])

/-- The exponent `-‖x‖²/2` splits as a sum of the one-dimensional exponents `-(xᵢ²/2)`. -/
private lemma neg_norm_sq_div_two {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    -‖x‖ ^ 2 / 2 = ∑ i, -((x i) ^ 2 / 2) := by
  rw [norm_sq_eq_sum_sq, Finset.sum_neg_distrib, ← Finset.sum_div]
  ring

/-- The multivariate Hermite polynomials `∏ᵢ H_{αᵢ}(xᵢ)` are orthogonal and their squared
`L²`-norm with respect to the (unnormalised) Gaussian weight `exp(-‖x‖²/2)` equals
`(∏ᵢ αᵢ!) · (√(2π))^m`. -/
theorem multivariate_hermite_norm {m : ℕ} (α : Fin m → ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin m),
        (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) ^ 2
        * Real.exp (-‖x‖ ^ 2 / 2))
      = (∏ i, ((α i).factorial : ℝ)) * Real.sqrt (2 * Real.pi) ^ m := by
  -- The one-dimensional factor attached to the coordinate `i`.
  let f : (i : Fin m) → ℝ → ℝ := fun i t =>
    (Polynomial.aeval t (Polynomial.hermite (α i))) ^ 2 * Real.exp (-(t ^ 2 / 2))
  -- The product integrand on `Fin m → ℝ`.
  let g : (Fin m → ℝ) → ℝ := fun y => ∏ i, f i (y i)
  -- Splitting the square of the product and the exponential of the sum.
  have hpow : ∀ x : EuclideanSpace ℝ (Fin m),
      (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)
        = ∏ i, (Polynomial.aeval (x i) (Polynomial.hermite (α i))) ^ 2
            * Real.exp (-((x i) ^ 2 / 2)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_pow, ← Real.exp_sum, neg_norm_sq_div_two x]
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin m),
      (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)
        = g (WithLp.ofLp x) := by
    intro x
    rw [hpow x]
  -- Step 1: transport the Lebesgue integral from `EuclideanSpace ℝ (Fin m)` to `Fin m → ℝ`.
  have hA : (∫ x : EuclideanSpace ℝ (Fin m),
        (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2))
      = ∫ y : Fin m → ℝ, g y := by
    rw [show (∫ x : EuclideanSpace ℝ (Fin m),
          (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2))
        = ∫ x : EuclideanSpace ℝ (Fin m), g (WithLp.ofLp x) from
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    exact MeasureTheory.MeasurePreserving.integral_comp'
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
      (ν := (volume : Measure (Fin m → ℝ)))
      (f := (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm)
      (PiLp.volume_preserving_ofLp (Fin m)) g
  rw [hA]
  -- Step 2: Fubini for the finite product measure — the integral factorises.
  have hB : (∫ y : Fin m → ℝ, g y) = ∏ i, ∫ x : ℝ, f i x := by
    rw [show (∫ y : Fin m → ℝ, g y) = ∫ y : Fin m → ℝ, ∏ i, f i (y i) from rfl]
    exact MeasureTheory.integral_fintype_prod_volume_eq_prod f
  rw [hB]
  -- Step 3: each one-dimensional factor is the `L²`-norm of `H_{αᵢ}`.
  have hC : (∏ i, ∫ x : ℝ, f i x)
      = ∏ i, ((α i).factorial : ℝ) * Real.sqrt (2 * Real.pi) := by
    apply Finset.prod_congr rfl
    intro i _
    exact hermite_gaussian_norm (α i)
  rw [hC]
  -- Step 4: combine the product of the constants.
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp

end

end Commons.Analysis.GaussianMeasure