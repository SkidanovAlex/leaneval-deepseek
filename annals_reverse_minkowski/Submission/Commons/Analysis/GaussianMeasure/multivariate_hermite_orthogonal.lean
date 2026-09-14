import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.hermite_gaussian_orthogonal

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory

/-- Integrals over the standard Gaussian measure on `ℝ^m = EuclideanSpace ℝ (Fin m)` of a
product of functions depending on a single coordinate factorize as the product of the
one-dimensional Gaussian integrals. -/
theorem integral_prod_gaussian_volume {m : ℕ} (f : Fin m → ℝ → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin m), (∏ i, f i (x i)) * Real.exp (-‖x‖ ^ 2 / 2))
      = ∏ i, ∫ t : ℝ, f i t * Real.exp (-(t ^ 2 / 2)) := by
  have hchange : (∫ x : EuclideanSpace ℝ (Fin m),
        (∏ i, f i (x i)) * Real.exp (-‖x‖ ^ 2 / 2))
      = ∫ y : Fin m → ℝ, (∏ i, f i (y i)) * Real.exp (-(∑ i, y i ^ 2) / 2) := by
    rw [← (PiLp.volume_preserving_toLp (Fin m)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding _]
    apply integral_congr_ae
    filter_upwards with y
    rw [EuclideanSpace.real_norm_sq_eq]
  rw [hchange]
  rw [show (∫ y : Fin m → ℝ, (∏ i, f i (y i)) * Real.exp (-(∑ i, y i ^ 2) / 2))
      = ∫ y : Fin m → ℝ, ∏ i, (f i (y i) * Real.exp (-(y i ^ 2 / 2))) from by
    apply integral_congr_ae
    filter_upwards with y
    have hexp : Real.exp (-(∑ i, y i ^ 2) / 2) = ∏ i, Real.exp (-(y i ^ 2 / 2)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [neg_div, Finset.sum_neg_distrib, Finset.sum_div]
    rw [hexp, ← Finset.prod_mul_distrib]]
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (E := fun _ : Fin m => ℝ)
      (fun i t => f i t * Real.exp (-(t ^ 2 / 2)))]

/-- Orthogonality of multivariate Hermite polynomials with respect to the standard Gaussian
weight on `ℝ^m`: the integral of a product of Hermite polynomials with two different
multi-indices `α ≠ β` vanishes. -/
theorem multivariate_hermite_orthogonal {m : ℕ} (α β : Fin m → ℕ) (h : α ≠ β) :
    (∫ x : EuclideanSpace ℝ (Fin m),
        (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i)))
        * (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (β i)))
        * Real.exp (-‖x‖ ^ 2 / 2)) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  rw [show (∫ x : EuclideanSpace ℝ (Fin m),
        (∏ j, Polynomial.aeval (x j) (Polynomial.hermite (α j)))
        * (∏ j, Polynomial.aeval (x j) (Polynomial.hermite (β j)))
        * Real.exp (-‖x‖ ^ 2 / 2))
      = ∫ x : EuclideanSpace ℝ (Fin m),
        (∏ j, (Polynomial.aeval (x j) (Polynomial.hermite (α j))
          * Polynomial.aeval (x j) (Polynomial.hermite (β j))))
        * Real.exp (-‖x‖ ^ 2 / 2) from by
    apply integral_congr_ae
    filter_upwards with x
    rw [← Finset.prod_mul_distrib]]
  rw [integral_prod_gaussian_volume (fun j t => Polynomial.aeval t (Polynomial.hermite (α j))
      * Polynomial.aeval t (Polynomial.hermite (β j)))]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hermite_gaussian_orthogonal hi)

end Commons.Analysis.GaussianMeasure
