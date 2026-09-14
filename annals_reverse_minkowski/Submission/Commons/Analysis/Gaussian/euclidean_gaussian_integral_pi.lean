import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace Commons.Analysis.Gaussian

theorem euclidean_gaussian_integral_pi (k : ℕ) (σ : ℝ) (hσ : 0 < σ) :
    (∫ x : EuclideanSpace ℝ (Fin k), Real.exp (-(Real.pi * ‖x‖ ^ 2 / σ ^ 2))) = σ ^ k := by
  have hb : 0 < Real.pi / σ ^ 2 := by positivity
  have h1 : (∫ x : EuclideanSpace ℝ (Fin k), Real.exp (-(Real.pi * ‖x‖ ^ 2 / σ ^ 2)))
      = ∫ x : EuclideanSpace ℝ (Fin k), Real.exp (-(Real.pi / σ ^ 2) * ‖x‖ ^ 2) := by
    congr with x
    congr 1
    ring
  rw [h1]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin k)) hb]
  rw [finrank_euclideanSpace_fin]
  have hdiv : Real.pi / (Real.pi / σ ^ 2) = σ ^ 2 := by
    field_simp
  rw [hdiv]
  have hsq : (σ ^ 2 : ℝ) ^ ((k : ℝ) / 2) = σ ^ k := by
    rw [← Real.rpow_natCast_mul (le_of_lt hσ) 2 ((k : ℝ) / 2)]
    rw [show ((2 : ℕ) : ℝ) * ((k : ℝ) / 2) = (k : ℝ) by push_cast; ring]
    exact Real.rpow_natCast σ k
  exact hsq

end Commons.Analysis.Gaussian