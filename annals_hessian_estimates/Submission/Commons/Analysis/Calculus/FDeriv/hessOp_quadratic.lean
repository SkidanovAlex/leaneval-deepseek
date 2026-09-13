import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace

/-- First derivative of the quadratic form `y ↦ ⟪A y, y⟫` for a symmetric operator `A`:
it is `2 • ⟪A x, ·⟫`. -/
theorem hessOp_quadratic_first_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (hA : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y)) (x : E) :
    fderiv ℝ (fun y : E => inner ℝ (A y) y) x = 2 • innerSL ℝ (A x) := by
  ext y
  rw [fderiv_inner_apply ℝ (f := fun t : E => A t) (g := fun t : E => t)
        A.differentiableAt differentiableAt_id y]
  rw [show fderiv ℝ (fun t : E => A t) x = A from ContinuousLinearMap.fderiv A]
  rw [show fderiv ℝ (fun t : E => t) x = ContinuousLinearMap.id ℝ E from fderiv_id]
  simp only [ContinuousLinearMap.id_apply, smul_apply, innerSL_apply_apply]
  rw [real_inner_comm x (A y), ← hA x y]
  ring

/-- The Hessian operator of the quadratic function `y ↦ ⟪A y, y⟫ / 2 + L y + c`, where `A` is
a self-adjoint continuous linear operator, is `A` itself. -/
theorem hessOp_quadratic {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hA : ∀ x y : E, inner ℝ (A x) y = inner ℝ x (A y))
    (L : E →L[ℝ] ℝ) (c : ℝ) (x : E) :
    InnerProductSpace.continuousLinearMapOfBilin
      (fderiv ℝ (fderiv ℝ (fun y : E => inner ℝ (A y) y / 2 + L y + c)) x) = A := by
  -- The derivative of `y ↦ ⟪A y, y⟫` is `2 • ⟪A x, ·⟫` everywhere.
  have hF : fderiv ℝ (fun y : E => inner ℝ (A y) y) = fun y => 2 • innerSL ℝ (A y) :=
    funext fun y => hessOp_quadratic_first_deriv A hA y
  have hFdiff : ∀ y : E, DifferentiableAt ℝ (fun z : E => inner ℝ (A z) z) y :=
    fun y => (A.differentiableAt).inner ℝ differentiableAt_id
  -- Halving the quadratic form divides its derivative by two.
  have hG : fderiv ℝ (fun y : E => inner ℝ (A y) y / 2) = fun y => innerSL ℝ (A y) := by
    funext y
    rw [show (fun z : E => inner ℝ (A z) z / 2)
          = (2⁻¹ : ℝ) • (fun z : E => inner ℝ (A z) z) by
        ext z; simp only [Pi.smul_apply, smul_eq_mul]; ring]
    rw [fderiv_const_smul (hFdiff y) (2⁻¹ : ℝ)]
    rw [hF]
    ext z
    simp only [smul_apply, smul_eq_mul]
    ring
  have hGdiff : ∀ y : E, DifferentiableAt ℝ (fun z : E => inner ℝ (A z) z / 2) y := by
    intro y
    have h : (fun z : E => inner ℝ (A z) z / 2)
        = (2⁻¹ : ℝ) • (fun z : E => inner ℝ (A z) z) := by
      ext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [h]
    exact (hFdiff y).const_smul (2⁻¹ : ℝ)
  -- First derivative of the full function `f`.
  have hdf : fderiv ℝ (fun y : E => inner ℝ (A y) y / 2 + L y + c)
      = fun y => innerSL ℝ (A y) + L := by
    funext y
    have h1 : HasFDerivAt (fun z : E => inner ℝ (A z) z / 2) (innerSL ℝ (A y)) y := by
      have h := (hGdiff y).hasFDerivAt
      rwa [show fderiv ℝ (fun z : E => inner ℝ (A z) z / 2) y = innerSL ℝ (A y)
            from congrFun hG y] at h
    have h2 : HasFDerivAt (fun z : E => inner ℝ (A z) z / 2 + L z + c)
        (innerSL ℝ (A y) + L) y := by
      have h := (h1.add L.hasFDerivAt).add_const c
      simpa only [Pi.add_apply] using h
    exact h2.fderiv
  -- The derivative of `y ↦ innerSL ℝ (A y) + L` is `(innerSL ℝ).comp A`.
  have hΦ : ∀ y : E, HasFDerivAt (fun y : E => innerSL ℝ (A y) + L)
      ((innerSL ℝ).comp A) y := by
    intro y
    have h1 : HasFDerivAt (fun y : E => ((innerSL ℝ).comp A) y) ((innerSL ℝ).comp A) y :=
      ContinuousLinearMap.hasFDerivAt ((innerSL ℝ).comp A)
    have h2 := h1.add_const L
    simpa [ContinuousLinearMap.comp_apply] using h2
  have hB : fderiv ℝ (fderiv ℝ (fun y : E => inner ℝ (A y) y / 2 + L y + c)) x
      = (innerSL ℝ).comp A := by
    rw [hdf]
    exact (hΦ x).fderiv
  -- Conclude using the Riesz representation characterisation of `continuousLinearMapOfBilin`.
  rw [hB]
  apply ContinuousLinearMap.ext
  intro v
  refine (InnerProductSpace.unique_continuousLinearMapOfBilin
    (B := (innerSL ℝ).comp A) (v := v) (f := A v) ?_).symm
  intro w
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]

end Commons.Analysis.Calculus.FDeriv