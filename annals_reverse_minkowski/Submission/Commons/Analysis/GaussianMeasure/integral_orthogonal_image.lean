import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory
open scoped Real BigOperators

/-- The linear map `Matrix.toLpLin 2 2 U` associated with an orthogonal matrix `U`
(i.e. `Uᵀ * U = 1`) is an isometry of Euclidean space. -/
theorem norm_toLpLin_of_transpose_mul_eq_one {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.transpose * U = 1) (x : EuclideanSpace ℝ (Fin n)) :
    ‖(Matrix.toLpLin 2 2 U) x‖ = ‖x‖ := by
  have hSS : ∀ w : Fin n → ℝ, ∑ i, w i ^ 2 = w ⬝ᵥ w := fun w => by
    rw [dotProduct]
    exact Finset.sum_congr rfl (fun i _ => by rw [pow_two])
  have hsq : ‖(Matrix.toLpLin 2 2 U) x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [Matrix.toLpLin_apply, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    rw [hSS, hSS (WithLp.ofLp x)]
    rw [← Matrix.dotProduct_transpose_mulVec (A := U) (x := WithLp.ofLp x) (y := Matrix.mulVec U (WithLp.ofLp x))]
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem integral_orthogonal_image {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.transpose * U = 1) (K : Set (EuclideanSpace ℝ (Fin n))) :
    ∫ x in (Matrix.toLpLin 2 2 U) '' K, Real.exp (-Real.pi * ‖x‖ ^ 2)
      = ∫ x in K, Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  classical
  have hTnorm : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖(Matrix.toLpLin 2 2 U) x‖ = ‖x‖ := norm_toLpLin_of_transpose_mul_eq_one U hU
  have hTinj : Function.Injective (Matrix.toLpLin 2 2 U) := by
    intro x y hxy
    have h0 : (Matrix.toLpLin 2 2 U) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 : ‖x - y‖ = 0 := by rw [← hTnorm (x - y), h0, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h1)
  have hTsurj : Function.Surjective (Matrix.toLpLin 2 2 U) :=
    (LinearMap.injective_iff_surjective).mp hTinj
  let Tli : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toLinearMap := Matrix.toLpLin 2 2 U
      norm_map' := hTnorm }
  let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.ofSurjective Tli hTsurj
  have hmp : MeasurePreserving (Matrix.toLpLin 2 2 U) volume volume := e.measurePreserving
  have hemb : MeasurableEmbedding (Matrix.toLpLin 2 2 U) := e.toHomeomorph.measurableEmbedding
  let G : EuclideanSpace ℝ (Fin n) → ℝ := fun z => Real.exp (-Real.pi * ‖z‖ ^ 2)
  change ∫ x in (Matrix.toLpLin 2 2 U) '' K, G x = ∫ x in K, G x
  have hpre : (Matrix.toLpLin 2 2 U) ⁻¹' ((Matrix.toLpLin 2 2 U) '' K) = K := by
    ext x; constructor
    · rintro ⟨y, hy, hyx⟩; exact hTinj hyx ▸ hy
    · intro hx; exact ⟨x, hx, rfl⟩
  have hrestrict : (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        ((Matrix.toLpLin 2 2 U) '' K)
      = Measure.map (Matrix.toLpLin 2 2 U)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) := by
    have h1 := hemb.restrict_map (volume : Measure (EuclideanSpace ℝ (Fin n)))
      ((Matrix.toLpLin 2 2 U) '' K)
    rw [hmp.map_eq, hpre] at h1
    exact h1
  calc ∫ x in (Matrix.toLpLin 2 2 U) '' K, G x
      = ∫ x, G x ∂(Measure.map (Matrix.toLpLin 2 2 U)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K)) := by
          rw [hrestrict]
    _ = ∫ x, G ((Matrix.toLpLin 2 2 U) x)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) :=
          hemb.integral_map G
    _ = ∫ x, G x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) :=
          integral_congr_ae (Filter.Eventually.of_forall (fun x => by
            simp only [G, hTnorm x]))
    _ = ∫ x in K, G x := rfl

end Commons.Analysis.GaussianMeasure
