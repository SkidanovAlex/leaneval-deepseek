import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.ou_hermite_eigenfunction

open MeasureTheory Polynomial
open scoped BigOperators

namespace Commons.Analysis.GaussianMeasure

noncomputable section

/-- Fubini's theorem for functions of the coordinates of a Euclidean space indexed by a finite
type: the integral over `EuclideanSpace ℝ ι` of a product of functions, each depending on a
single coordinate, is the product of the integrals. -/
theorem integral_euclideanSpace_prod_coord_real {ι : Type*} [Fintype ι]
    (h : ι → ℝ → ℝ) :
    (∫ v : EuclideanSpace ℝ ι, ∏ j, h j (v j)) = ∏ j, ∫ x : ℝ, h j x := by
  have key : (∫ v : EuclideanSpace ℝ ι, ∏ j, h j (v j)) = ∫ w : ι → ℝ, ∏ j, h j (w j) := by
    have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).integral_comp'
      (fun w : ι → ℝ ↦ ∏ j, h j (w j))
    simpa using this
  rw [key]
  exact integral_fintype_prod_volume_eq_prod (fun j ↦ h j)

/-- `(1/√x)^m = 1/x^(m/2)` for `x > 0`. -/
private lemma inv_sqrt_pow_eq (x : ℝ) (hx : 0 < x) (m : ℕ) :
    (1 / Real.sqrt x) ^ m = 1 / x ^ ((m : ℝ) / 2) := by
  have h1 : 1 / Real.sqrt x = x ^ (-(1/2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hx.le]
  rw [h1, ← Real.rpow_natCast (x ^ (-(1/2 : ℝ))) m, ← Real.rpow_mul hx.le]
  rw [show (-(1/2:ℝ)) * (m:ℝ) = -((m:ℝ)/2) by ring]
  rw [Real.rpow_neg hx.le, one_div]

/-- The Gaussian exponent of a shifted Gaussian splits as a product over the coordinates. -/
private lemma exp_neg_norm_eq_prod {m : ℕ} (t D : ℝ) (v y : EuclideanSpace ℝ (Fin m)) :
    Real.exp (-‖y - (Real.exp (-t)) • v‖ ^ 2 / (2 * D))
      = ∏ i, Real.exp (-((y i - Real.exp (-t) * (v i)) ^ 2) / (2 * D)) := by
  rw [← Real.exp_sum]
  congr 1
  have hnorm : ‖y - (Real.exp (-t)) • v‖ ^ 2 = ∑ i, (y i - Real.exp (-t) * v i) ^ 2 := by
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
private lemma integrand_eq_prod {m : ℕ} (α : Fin m → ℕ) (t D : ℝ) (hD : 0 < D)
    (v y : EuclideanSpace ℝ (Fin m)) :
    (1 / (2 * Real.pi * D) ^ ((m : ℝ) / 2))
        * Real.exp (-‖y - (Real.exp (-t)) • v‖ ^ 2 / (2 * D))
        * (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i)))
    = ∏ i, ((1 / Real.sqrt (2 * Real.pi * D))
        * Real.exp (-((y i - Real.exp (-t) * (v i)) ^ 2) / (2 * D))
        * Polynomial.aeval (y i) (Polynomial.hermite (α i))) := by
  have hpos : 0 < 2 * Real.pi * D := by positivity
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← inv_sqrt_pow_eq (2 * Real.pi * D) hpos m]
  rw [← exp_neg_norm_eq_prod t D v y]

/-- **Multivariate Hermite eigenfunction identity.** The multivariate Mehler kernel applied to
`∏ᵢ He_{αᵢ}` reproduces `∏ᵢ He_{αᵢ}` up to the eigenvalue `exp (-(Σ αᵢ) t)`. -/
theorem ou_multivariate_hermite_eigenfunction {m : ℕ} (α : Fin m → ℕ) (t : ℝ)
    (v : EuclideanSpace ℝ (Fin m)) (ht : 0 < t) :
    (∫ y : EuclideanSpace ℝ (Fin m),
        (1 / (2 * Real.pi * (1 - Real.exp (-2 * t))) ^ ((m : ℝ) / 2))
          * Real.exp (-‖y - (Real.exp (-t)) • v‖ ^ 2 / (2 * (1 - Real.exp (-2 * t))))
          * (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))))
      = Real.exp (-(((∑ i, α i) : ℕ) : ℝ) * t)
          * (∏ i, Polynomial.aeval (v i) (Polynomial.hermite (α i))) := by
  have hD : 0 < 1 - Real.exp (-2 * t) := by
    rw [sub_pos, Real.exp_lt_one_iff]; linarith
  let G : Fin m → ℝ → ℝ := fun i u =>
    (1 / Real.sqrt (2 * Real.pi * (1 - Real.exp (-2 * t))))
      * Real.exp (-((u - Real.exp (-t) * (v i)) ^ 2) / (2 * (1 - Real.exp (-2 * t))))
      * Polynomial.aeval u (Polynomial.hermite (α i))
  have hcongr : (∫ y : EuclideanSpace ℝ (Fin m),
        (1 / (2 * Real.pi * (1 - Real.exp (-2 * t))) ^ ((m : ℝ) / 2))
          * Real.exp (-‖y - (Real.exp (-t)) • v‖ ^ 2 / (2 * (1 - Real.exp (-2 * t))))
          * (∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))))
      = ∫ y : EuclideanSpace ℝ (Fin m), ∏ i, G i (y i) := by
    apply integral_congr_ae
    filter_upwards with y
    exact integrand_eq_prod α t (1 - Real.exp (-2 * t)) hD v y
  rw [hcongr, integral_euclideanSpace_prod_coord_real G]
  have hGi : ∀ i, (∫ u : ℝ, G i u)
      = Real.exp (-((α i : ℕ) : ℝ) * t)
        * Polynomial.aeval (v i) (Polynomial.hermite (α i)) := by
    intro i
    exact ou_hermite_eigenfunction (α i) t (v i) ht
  rw [Finset.prod_congr rfl (fun i _ => hGi i)]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 1
  congr 1
  rw [← Finset.sum_mul, Finset.sum_neg_distrib, ← Nat.cast_sum]

end

end Commons.Analysis.GaussianMeasure
