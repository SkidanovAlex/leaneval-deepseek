import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Vertex
import Submission.Work.Smooth.BoxGeneric.Vertex.aeNoVertex_of_ae_centre

namespace Work.Smooth.BoxGeneric.LocalSurface

open LeanEval.KnotTheory.PardonDistortion

/-!
# The derivative of a signed face of the box in the vertex-ray direction

The signed faces `faceLin c σ i ε` of Pardon's box are affine functions of the point, so their
derivative is the constant linear functional `v ↦ ε * (v (σ i) / boxSide i)`.  Applying this at a
vertex `boxVertex c σ ε s` of the box, in the direction of the vertex ray `Vertex.vertexDir σ ε`,
gives `ε i * (ε i * boxSide i) / boxSide i = (ε i)^2 = 1`: **the vertex ray crosses the face
`(i, ε i)` of the box transversally, with unit speed**.  This is the tangency input `htan` of
`Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_vertex_tangent`.

## Main results

* `Work.Smooth.BoxGeneric.LocalSurface.coordLM`, `coordLM_apply` — the coordinate functional
  `y ↦ y i` of `R3 = EuclideanSpace ℝ (Fin 3)` as a continuous linear map;
* `Work.Smooth.BoxGeneric.LocalSurface.fderiv_faceLin_apply` — the derivative of a signed face;
* `Work.Smooth.BoxGeneric.LocalSurface.fderiv_pullback_faceLin_apply_vertexDir` — the target: the
  derivative of the pulled-back signed face in the vertex-ray direction is `1`.
-/

/-- The `i`-th coordinate functional `y ↦ y i` of `R3 = EuclideanSpace ℝ (Fin 3)`, as a continuous
linear map. -/
def coordLM (i : Fin 3) : R3 →L[ℝ] ℝ :=
  PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 3 => ℝ) i

@[simp] theorem coordLM_apply (i : Fin 3) (y : R3) : coordLM i y = y i := rfl

theorem hasFDerivAt_coordLM (i : Fin 3) (y : R3) :
    HasFDerivAt (fun y : R3 => y i) (coordLM i) y :=
  (coordLM i).hasFDerivAt

/-- The derivative of the `i`-th coordinate functional. -/
theorem fderiv_coordLM_apply (i : Fin 3) (y v : R3) :
    fderiv ℝ (fun y : R3 => y i) y v = v i := by
  rw [(hasFDerivAt_coordLM i y).fderiv, coordLM_apply]

/-- **The derivative of a signed face of the box.**  `faceLin c σ i ε` is affine, so its derivative
at every point is the constant linear functional `v ↦ ε * (v (σ i) / boxSide i)`. -/
theorem fderiv_faceLin_apply (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (ε : ℝ) (y v : R3) :
    fderiv ℝ (Work.Smooth.BoxGeneric.faceLin c σ i ε) y v =
      ε * (v (σ i) / Submission.boxSide i) := by
  have hfun : Work.Smooth.BoxGeneric.faceLin c σ i ε
      = fun z : R3 => ε * ((Submission.boxSide i)⁻¹ * (z (σ i) - c (σ i))) := by
    funext z
    simp only [Work.Smooth.BoxGeneric.faceLin_apply, Work.Smooth.BoxGeneric.signedFace,
      div_eq_mul_inv]
    ring
  rw [hfun]
  have h1 : HasFDerivAt (fun z : R3 => z (σ i) - c (σ i)) (coordLM (σ i)) y :=
    (hasFDerivAt_coordLM (σ i) y).sub_const (c (σ i))
  have h2 : HasFDerivAt (fun z : R3 => (Submission.boxSide i)⁻¹ * (z (σ i) - c (σ i)))
      ((Submission.boxSide i)⁻¹ • coordLM (σ i)) y :=
    h1.const_mul ((Submission.boxSide i)⁻¹)
  have h3 : HasFDerivAt
      (fun z : R3 => ε * ((Submission.boxSide i)⁻¹ * (z (σ i) - c (σ i))))
      (ε • ((Submission.boxSide i)⁻¹ • coordLM (σ i))) y :=
    h2.const_mul ε
  rw [h3.fderiv]
  simp only [smul_apply, coordLM_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem fderiv_pullback_faceLin_apply_vertexDir {ψ : Submission.Diffeo} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {ε : Fin 3 → ℝ} {s : ℝ} {p : ℝ × ℝ}
    (hp : Work.Smooth.Morse.param ψ p = Work.Smooth.BoxGeneric.boxVertex c σ ε s)
    {r : ℝ × ℝ} (hr : fderiv ℝ (Work.Smooth.Morse.param ψ) p r =
      Work.Smooth.BoxGeneric.Vertex.vertexDir σ ε)
    (i : Fin 3) (hε : ε i = 1 ∨ ε i = -1) :
    fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i))) p r = 1 := by
  -- the chain rule for the pull-back along the parametrisation of the surface
  have hcomp :
      fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i))) p
        = (fderiv ℝ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i))
              (Work.Smooth.Morse.param ψ p)).comp
            (fderiv ℝ (Work.Smooth.Morse.param ψ) p) :=
    fderiv_comp (𝕜 := ℝ) (f := Work.Smooth.Morse.param ψ)
      (g := Work.Smooth.BoxGeneric.faceLin c σ i (ε i)) p
      (((Work.Smooth.BoxGeneric.contDiff_faceLin c σ i (ε i)).differentiable (by simp)).differentiableAt)
      (((Work.Smooth.Morse.param_contDiff ψ).differentiable (by simp)).differentiableAt)
  -- the derivative of the face, evaluated at the vertex, in the vertex-ray direction
  rw [hcomp, ContinuousLinearMap.comp_apply, hr, hp, fderiv_faceLin_apply,
    Work.Smooth.BoxGeneric.Vertex.vertexDir_apply]
  simp only [Equiv.symm_apply_apply]
  have hb : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
  rcases hε with h | h <;> rw [h] <;> field_simp

end Work.Smooth.BoxGeneric.LocalSurface
