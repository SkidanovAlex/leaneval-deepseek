import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.Calculus

open scoped Real InnerProductSpace

/-- The slice map `z ↦ WithLp.toLp 2 (z, y)`, inserting a fixed second coordinate into the
`L²`-product `WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)`, is Fréchet differentiable at every
point, with derivative the composite of the canonical continuous linear equivalence
`WithLp.prodContinuousLinearEquiv` (in the direction `EuclideanSpace ℝ (Fin n) × ℝ →
WithLp 2 (⋯)`) with the left inclusion `v ↦ (v, 0)`. -/
lemma hasFDerivAt_toLp_prod_slice {n : ℕ} (y : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (z, y))
      ((↑(WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).symm :
          (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ)) u := by
  let e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).symm
  have hφ : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => (z, y))
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ) u := by
    have h := (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ).hasFDerivAt (x := u)
    have h2 := h.add_const (((0 : EuclideanSpace ℝ (Fin n)), y))
    simpa using h2
  have he : HasFDerivAt
      (⇑(e : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)))
      ((e : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)))
      ((fun z : EuclideanSpace ℝ (Fin n) => (z, y)) u) :=
    ContinuousLinearMap.hasFDerivAt
      (e : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))
  exact he.comp u hφ

theorem fderiv_comp_toLp_prod {n : ℕ}
    (f : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → ℝ) (hf : Differentiable ℝ f)
    (u : EuclideanSpace ℝ (Fin n)) (y : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => f (WithLp.toLp 2 (z, y))) u v
      = fderiv ℝ f (WithLp.toLp 2 (u, y)) (WithLp.toLp 2 (v, 0)) := by
  let e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).symm
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) :=
    e.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  have hg : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (z, y)) L u :=
    hasFDerivAt_toLp_prod_slice y u
  have hcomp : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => f (WithLp.toLp 2 (z, y)))
      ((fderiv ℝ f (WithLp.toLp 2 (u, y))).comp L) u :=
    (hf (WithLp.toLp 2 (u, y))).hasFDerivAt.comp u hg
  rw [hcomp.fderiv]
  have hLv : L v = WithLp.toLp 2 (v, (0 : ℝ)) := by simp [L, e]
  simp only [ContinuousLinearMap.comp_apply, hLv]

end Commons.Analysis.Calculus