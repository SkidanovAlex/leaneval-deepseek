import Mathlib
import Submission.Work.Projection.Basic

/-!
# The derivative of `(u, w) ↦ projVec u w`

`Work.Projection.projVec u : ℝ^{k+1} →L[ℝ] ℝ^k` is the projection with kernel spanned by
`(u, 1)`, given in coordinates by `(projVec u w) i = w i - u i * w (last)`.  It is *affine* in `u`
and *linear* in `w`, and this file computes its derivative, which is used to differentiate the
triple-point parametrisation of the projection of an embedded manifold.
-/

open scoped Manifold ContDiff
open Topology

namespace Work.Projection

/-- **The derivative of `(u, w) ↦ projVec u w`.**  The coordinate formula
`(projVec u w) i = w i - u i * w (last)` exhibits the map as a sum of a linear map (the first `k`
coordinates of `w`) and a bilinear one (`(w (last)) • u`), so its derivative at `(u, w)` is
`(δu, δw) ↦ projVec u δw - (w (last)) • δu`. -/
theorem hasFDerivAt_projVec_bilinear (k : ℕ) (u : EuclideanSpace ℝ (Fin k))
    (w : EuclideanSpace ℝ (Fin (k + 1))) :
    HasFDerivAt (fun x : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
        projVec x.1 x.2)
      ((projVec u).comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k))
          (EuclideanSpace ℝ (Fin (k + 1)))) -
        (w (Fin.last k)) • ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k))
          (EuclideanSpace ℝ (Fin (k + 1)))) (u, w) := by
  have hfst : ∀ x : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)),
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k))
        (EuclideanSpace ℝ (Fin (k + 1)))) x = x.1 := fun x => rfl
  have hsnd : ∀ x : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)),
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k))
        (EuclideanSpace ℝ (Fin (k + 1)))) x = x.2 := fun x => rfl
  have hdecomp : (fun x : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
        projVec x.1 x.2)
      = fun x : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
        projVec (0 : EuclideanSpace ℝ (Fin k)) x.2 - (x.2 (Fin.last k)) • x.1 := by
    funext x
    apply WithLp.ofLp_injective
    funext i
    simp only [projVec_apply]
    simp
    ring
  rw [hdecomp]
  have hA : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
      projVec (0 : EuclideanSpace ℝ (Fin k)) x.2)
      ((projVec (0 : EuclideanSpace ℝ (Fin k))).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k))
          (EuclideanSpace ℝ (Fin (k + 1))))) (u, w) :=
    ContinuousLinearMap.hasFDerivAt ((projVec (0 : EuclideanSpace ℝ (Fin k))).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k))
          (EuclideanSpace ℝ (Fin (k + 1)))))
  have hc : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
        x.2 (Fin.last k))
      ((EuclideanSpace.proj (Fin.last k)).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k))
          (EuclideanSpace ℝ (Fin (k + 1))))) (u, w) :=
    ContinuousLinearMap.hasFDerivAt ((EuclideanSpace.proj (Fin.last k)).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin k))
          (EuclideanSpace ℝ (Fin (k + 1)))))
  have hf : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (k + 1)) =>
        x.1)
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k))
        (EuclideanSpace ℝ (Fin (k + 1)))) (u, w) :=
    ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin k))
        (EuclideanSpace ℝ (Fin (k + 1))))
  have hB := hc.smul hf
  refine (hA.sub hB).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun x => ?_
  apply WithLp.ofLp_injective
  funext i
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, hfst, hsnd]
  simp
  ring

end Work.Projection
