import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Real MeasureTheory
open scoped Real

namespace Commons.Analysis.Fourier

/-- The real Gaussian `q ↦ exp(−b·‖q‖²)` is integrable on `ℝ³` for `b > 0`,
and its integral over all of `ℝ³` equals `(π / b) ^ (3 / 2)`. -/
theorem gauss_sq_integrable_volume {b : ℝ} (hb : 0 < b) :
    Integrable (fun q : EuclideanSpace ℝ (Fin 3) => Real.exp (-(b * ‖q‖ ^ 2))) ∧
      (∫ q : EuclideanSpace ℝ (Fin 3), Real.exp (-(b * ‖q‖ ^ 2))) =
        (Real.pi / b) ^ (3 / 2 : ℝ) := by
  let f : EuclideanSpace ℝ (Fin 3) → ℝ := fun q => Real.exp (-(b * ‖q‖ ^ 2))
  -- After the volume-preserving change of variables `EuclideanSpace ℝ (Fin 3) ≅ (Fin 3 → ℝ)`,
  -- the function factorizes as a product of three one-dimensional Gaussians.
  have hpoint : ∀ x : (Fin 3 → ℝ),
      f (WithLp.toLp 2 x) = ∏ i : Fin 3, Real.exp (-(b * (x i) ^ 2)) := by
    intro x
    dsimp [f]
    rw [EuclideanSpace.real_norm_sq_eq]
    have hsum : -(b * (∑ i : Fin 3, (x i) ^ 2)) = ∑ i : Fin 3, -(b * (x i) ^ 2) := by
      rw [← neg_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [neg_mul]
    rw [hsum]
    simpa using (Real.exp_sum (Finset.univ : Finset (Fin 3)) (fun i => -(b * (x i) ^ 2)))
  constructor
  · -- Integrability on the product side follows from the one-dimensional Gaussians, and the
    -- volume-preserving measurable equivalence transfers it to `EuclideanSpace`.
    have hfprod_int :
        Integrable (fun x : (Fin 3 → ℝ) => ∏ i : Fin 3, Real.exp (-(b * (x i) ^ 2))) := by
      have h1d : ∀ i : Fin 3, Integrable (fun x : ℝ => Real.exp (-(b * x ^ 2))) := by
        intro i
        simpa [neg_mul] using (integrable_exp_neg_mul_sq hb)
      exact Integrable.fintype_prod (ι := Fin 3) (E := ℝ)
        (μ := fun _ : Fin 3 => (volume : Measure ℝ))
        (f := fun i (x : ℝ) => Real.exp (-(b * x ^ 2))) h1d
    have hfto_int : Integrable (fun x : (Fin 3 → ℝ) => f (WithLp.toLp 2 x)) := by
      rw [show (fun x : (Fin 3 → ℝ) => f (WithLp.toLp 2 x)) =
          (fun x : (Fin 3 → ℝ) => ∏ i : Fin 3, Real.exp (-(b * (x i) ^ 2))) from
        funext (fun x => hpoint x)]
      exact hfprod_int
    have hiff : Integrable (fun x : (Fin 3 → ℝ) => f (WithLp.toLp 2 x)) ↔ Integrable f :=
      (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb (g := f)
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    change Integrable f
    exact hiff.mp hfto_int
  · -- The integral is the well-known multivariate Gaussian integral.
    have h1 := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin 3)) hb
    rw [finrank_euclideanSpace_fin] at h1
    simpa [neg_mul] using h1

end Commons.Analysis.Fourier