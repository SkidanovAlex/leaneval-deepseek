import Mathlib
import Submission.Work.Drive.Generic.HeightDefs
import Submission.Work.Drive.Generic.inner_fderiv_normal_d2

/-!
# The differential of the Gauss parametrisation

For a `C³` plane curve `Φ`, the Gauss parametrisation is `gaussParam Φ z = z 2 • normal Φ (z 0, z 1)`
(see `HeightDefs`).  This file computes its differential: since multiplication by the (linear)
scalar function `z ↦ z 2` and the composed Gauss map `z ↦ normal Φ (z 0, z 1)` are both
differentiable, the product rule gives

`d(gaussParam Φ)(z) y = (y 2) • normal Φ (z 0, z 1) + (z 2) • d(normal Φ)(z 0, z 1) (y 0, y 1)`.

The derivative of the composed Gauss map is the chain rule applied to the linear projection
`z ↦ (z 0, z 1)`, whose differential is computed in `fderiv_pairE3` below.
-/

namespace Work.Drive.Generic

open scoped Matrix RealInnerProductSpace
open MeasureTheory

/-- The coordinate functional `z ↦ z i` of `E3` is `EuclideanSpace.proj i`. -/
lemma coordE3_apply (i : Fin 3) (w : E3) :
    (EuclideanSpace.proj (𝕜 := ℝ) i : E3 →L[ℝ] ℝ) w = w i := by
  simp [EuclideanSpace.proj, PiLp.proj, PiLp.projₗ]

/-- The projection `z ↦ (z 0, z 1)`, as a continuous linear map. -/
noncomputable def projE3 : E3 →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) 0).prod (EuclideanSpace.proj (𝕜 := ℝ) 1)

@[simp] lemma projE3_apply (w : E3) : projE3 w = (w 0, w 1) := by
  simp [projE3, ContinuousLinearMap.prod_apply]

/-- The differential of the projection `z ↦ (z 0, z 1)` is that projection. -/
lemma fderiv_pairE3 (z : E3) :
    HasFDerivAt (fun z : E3 => (z 0, z 1)) projE3 z :=
  (ContinuousLinearMap.hasFDerivAt projE3).congr_of_eventuallyEq
    (Filter.EventuallyEq.of_eq (funext (fun w => (projE3_apply w).symm)))

/-- The differential of the coordinate function `z ↦ z i` is `EuclideanSpace.proj i`. -/
lemma fderiv_coordE3 (z : E3) (i : Fin 3) :
    HasFDerivAt (fun z : E3 => z i) (EuclideanSpace.proj (𝕜 := ℝ) i) z :=
  (ContinuousLinearMap.hasFDerivAt (EuclideanSpace.proj (𝕜 := ℝ) i)).congr_of_eventuallyEq
    (Filter.EventuallyEq.of_eq (funext (fun w => (coordE3_apply i w).symm)))

/-- The differential of the composed Gauss map `z ↦ normal Φ (z 0, z 1)`. -/
lemma hasFDerivAt_normal_compE3 {Φ : ℝ × ℝ → E3} (hΦ : ContDiff ℝ 3 Φ) (z : E3) :
    HasFDerivAt (fun z : E3 => normal Φ (z 0, z 1))
      ((fderiv ℝ (normal Φ) (z 0, z 1)).comp projE3) z := by
  have hNpt : HasFDerivAt (normal Φ) (fderiv ℝ (normal Φ) (z 0, z 1)) (z 0, z 1) :=
    (hasFDerivAt_normal hΦ (z 0, z 1)).differentiableAt.hasFDerivAt
  exact hNpt.comp z (fderiv_pairE3 z)

/-- The product rule for the Gauss parametrisation, in `HasFDerivAt` form. -/
lemma hasFDerivAt_gaussParam {Φ : ℝ × ℝ → E3} (hΦ : ContDiff ℝ 3 Φ) (z : E3) :
    HasFDerivAt (gaussParam Φ)
      ((z 2) • (fderiv ℝ (normal Φ) (z 0, z 1)).comp projE3 +
        (EuclideanSpace.proj (𝕜 := ℝ) 2).smulRight (normal Φ (z 0, z 1))) z := by
  have hf : HasFDerivAt (fun z : E3 => normal Φ (z 0, z 1))
      ((fderiv ℝ (normal Φ) (z 0, z 1)).comp projE3) z := hasFDerivAt_normal_compE3 hΦ z
  have hc : HasFDerivAt (fun z : E3 => z 2) (EuclideanSpace.proj (𝕜 := ℝ) 2) z :=
    fderiv_coordE3 z 2
  have h : HasFDerivAt (fun z : E3 => (z 2) • normal Φ (z 0, z 1))
      ((fun z : E3 => z 2) z • ((fderiv ℝ (normal Φ) (z 0, z 1)).comp projE3) +
        (EuclideanSpace.proj (𝕜 := ℝ) 2).smulRight ((fun z : E3 => normal Φ (z 0, z 1)) z)) z :=
    hc.smul hf
  change HasFDerivAt (fun z : E3 => (z 2) • normal Φ (z 0, z 1))
      ((z 2) • (fderiv ℝ (normal Φ) (z 0, z 1)).comp projE3 +
        (EuclideanSpace.proj (𝕜 := ℝ) 2).smulRight (normal Φ (z 0, z 1))) z
  exact h

/-- The differential of the Gauss parametrisation: the product rule
`d(z 2 • N(z 0, z 1)) = (dz 2) • N + (z 2) • dN`, with `dz 2` the coordinate functional. -/
theorem fderiv_gaussParam {Φ : ℝ × ℝ → Work.Drive.Generic.E3} (hΦ : ContDiff ℝ 3 Φ)
    (z y : Work.Drive.Generic.E3) :
    fderiv ℝ (Work.Drive.Generic.gaussParam Φ) z y =
      (y 2) • Work.Drive.Generic.normal Φ (z 0, z 1) +
        (z 2) • fderiv ℝ (Work.Drive.Generic.normal Φ) (z 0, z 1) (y 0, y 1) := by
  have h := (hasFDerivAt_gaussParam hΦ z).fderiv
  have h2 := congrArg (fun (L : E3 →L[ℝ] E3) => L y) h
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply] at h2
  rw [projE3_apply y, coordE3_apply 2 y] at h2
  rw [h2]
  exact add_comm _ _

end Work.Drive.Generic
