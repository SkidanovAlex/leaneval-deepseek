import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.ou_hermite_eigenfunction
import Submission.Commons.Analysis.GaussianMeasure.ou_multivariate_hermite_eigenfunction

open MeasureTheory Polynomial
open scoped BigOperators

namespace Commons.Analysis.GaussianMeasure

noncomputable section

/-- `(1/√x)^m = 1/x^(m/2)` for `x > 0`. -/
private lemma inv_sqrt_pow_eq_gen (x : ℝ) (hx : 0 < x) (m : ℕ) :
    (1 / Real.sqrt x) ^ m = 1 / x ^ ((m : ℝ) / 2) := by
  have h1 : 1 / Real.sqrt x = x ^ (-(1/2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hx.le]
  rw [h1, ← Real.rpow_natCast (x ^ (-(1/2 : ℝ))) m, ← Real.rpow_mul hx.le]
  rw [show (-(1/2:ℝ)) * (m:ℝ) = -((m:ℝ)/2) by ring]
  rw [Real.rpow_neg hx.le, one_div]

/-- The Gaussian exponent of a shifted Gaussian splits as a product over the coordinates. -/
private lemma exp_neg_norm_eq_prod_gen {m : ℕ} (r D : ℝ) (v y : EuclideanSpace ℝ (Fin m)) :
    Real.exp (-‖y - r • v‖ ^ 2 / (2 * D))
      = ∏ i, Real.exp (-((y.ofLp i - r * (v.ofLp i)) ^ 2) / (2 * D)) := by
  rw [← Real.exp_sum]
  congr 1
  have hnorm : ‖y - r • v‖ ^ 2 = ∑ i, (y.ofLp i - r * v.ofLp i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hnorm, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_div]

/-- The integrand of the multivariate Mehler kernel is the product of the corresponding
one-dimensional integrands. -/
private lemma integrand_eq_prod_gen {m : ℕ} (α : Fin m → ℕ) (r D : ℝ) (hD : 0 < D)
    (v y : EuclideanSpace ℝ (Fin m)) :
    (1 / (2 * Real.pi * D) ^ ((m : ℝ) / 2))
        * Real.exp (-‖y - r • v‖ ^ 2 / (2 * D))
        * (∏ i, Polynomial.aeval (y.ofLp i) (Polynomial.hermite (α i)))
    = ∏ i, ((1 / Real.sqrt (2 * Real.pi * D))
        * Real.exp (-((y.ofLp i - r * (v.ofLp i)) ^ 2) / (2 * D))
        * Polynomial.aeval (y.ofLp i) (Polynomial.hermite (α i))) := by
  have hpos : 0 < 2 * Real.pi * D := by positivity
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← inv_sqrt_pow_eq_gen (2 * Real.pi * D) hpos m]
  rw [← exp_neg_norm_eq_prod_gen r D v y]

/-- **Multivariate Hermite eigenfunction identity (general parameter).** The multivariate
Mehler kernel with parameter `r` (`|r| < 1`) applied to `∏ᵢ He_{αᵢ}` reproduces
`∏ᵢ He_{αᵢ}` up to the eigenvalue `r^(Σ αᵢ)`. -/
theorem ou_multivariate_hermite_eigenfunction_gen {N : ℕ} (α : Fin N → ℕ) (r : ℝ)
    (hr : r ^ 2 < 1) (v : EuclideanSpace ℝ (Fin N)) :
    (∫ y : EuclideanSpace ℝ (Fin N), (1 / (2 * Real.pi * (1 - r ^ 2)) ^ ((N : ℝ) / 2))
        * Real.exp (-‖y - r • v‖ ^ 2 / (2 * (1 - r ^ 2)))
        * (∏ i, Polynomial.aeval (y.ofLp i) (Polynomial.hermite (α i))))
      = r ^ ((∑ i, α i) : ℕ) * (∏ i, Polynomial.aeval (v.ofLp i) (Polynomial.hermite (α i))) := by
  have hD : 0 < 1 - r ^ 2 := by linarith
  let G : Fin N → ℝ → ℝ := fun i u =>
    (1 / Real.sqrt (2 * Real.pi * (1 - r ^ 2)))
      * Real.exp (-((u - r * (v.ofLp i)) ^ 2) / (2 * (1 - r ^ 2)))
      * Polynomial.aeval u (Polynomial.hermite (α i))
  have hcongr : (∫ y : EuclideanSpace ℝ (Fin N),
        (1 / (2 * Real.pi * (1 - r ^ 2)) ^ ((N : ℝ) / 2))
          * Real.exp (-‖y - r • v‖ ^ 2 / (2 * (1 - r ^ 2)))
          * (∏ i, Polynomial.aeval (y.ofLp i) (Polynomial.hermite (α i))))
      = ∫ y : EuclideanSpace ℝ (Fin N), ∏ i, G i (y.ofLp i) := by
    apply integral_congr_ae
    filter_upwards with y
    exact integrand_eq_prod_gen α r (1 - r ^ 2) hD v y
  rw [hcongr, integral_euclideanSpace_prod_coord_real G]
  have hGi : ∀ i, (∫ u : ℝ, G i u)
      = r ^ (α i) * Polynomial.aeval (v.ofLp i) (Polynomial.hermite (α i)) := by
    intro i
    have hs : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr hD
    have hsq : (Real.sqrt (1 - r ^ 2)) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hD.le
    have h := ou_hermite_gen (α i) r (Real.sqrt (1 - r ^ 2)) (v.ofLp i) hs hsq
    rw [Real.sq_sqrt hD.le] at h
    simpa only [G] using h
  rw [Finset.prod_congr rfl (fun i _ => hGi i)]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum]

end

end Commons.Analysis.GaussianMeasure
