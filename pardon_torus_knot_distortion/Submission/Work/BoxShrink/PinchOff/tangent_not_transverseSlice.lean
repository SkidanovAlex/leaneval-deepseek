import Mathlib
import Submission.Work.BoxShrink.PinchOff.TangentConfig

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- The pull-back of the plane coordinate at the tangent configuration is the first coordinate of
the standard torus parametrisation: `planeG idDiffeo (1,0,0) (0 1 2) 0 (x,y) =
(2 + cos y) cos x - 1`. -/
theorem planeG_idDiffeo_tangent :
    Work.BoxShrink.Pinch.planeG idDiffeo tangentCtr tangentCyc3 0
      = fun p : ℝ × ℝ => (2 + Real.cos p.2) * Real.cos p.1 - 1 := by
  funext p
  rw [Work.BoxShrink.Pinch.planeG_apply, Work.BoxShrink.Bubble.planeCoord_apply,
    Work.BoxShrink.Pinch.par_apply]
  simp only [tangentCyc3_two, tangentCtr_zero, idDiffeo, id_eq]
  norm_num

/-- The derivative of the explicit function `(x,y) ↦ (2 + cos y) cos x - 1`. -/
theorem fderiv_tangent_planeG (p : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => (2 + Real.cos p.2) * Real.cos p.1 - 1) p
      = (2 + Real.cos p.2) • ((-Real.sin p.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ))
        + Real.cos p.1 • ((-Real.sin p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  have hA : HasFDerivAt (fun x : ℝ × ℝ => 2 + Real.cos x.2)
      ((-Real.sin p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ)).cos).const_add 2
  have hB : HasFDerivAt (fun x : ℝ × ℝ => Real.cos x.1)
      ((-Real.sin p.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ ℝ ℝ)).cos
  exact ((hA.mul hB).sub_const 1).fderiv

-- The tangent configuration of the box `PBox (13/10) (1,0,0) (0 1 2)` with the cutting plane
-- `{x = 1}` is NOT transverse: at the parameter point `p = (0, π)` (the inner-equator point
-- `(1,0,0)`, where the plane is tangent to the standard torus) one has `boxB p < 13/10`,
-- `planeG p = 0` and `fderiv ℝ (planeG …) p = 0`.
-- Concretely `planeG idDiffeo tangentCtr tangentCyc3 0 (x,y) = (2 + cos y) * cos x - 1`
-- (the first coordinate of `torusMap`), whence `∂/∂x = -(2 + cos y) sin x` and
-- `∂/∂y = -(sin y) cos x` both vanish at `(0, π)`.
-- This is what makes the refutation of `Key`/`SmoothHalfS` in `KeyRefuted.lean` consistent with
-- the tamed residual `Work.BoxShrink.Pinch.PushOffHalfTame` (which carries `TransverseSlice`).
theorem tangent_not_transverseSlice :
    ¬ Work.BoxShrink.Pinch.TransverseSlice idDiffeo tangentRad tangentCtr tangentCyc3 0 := by
  intro h
  -- the parameter point `(0, π)` of the inner equator, where `torusMap 0 π = (1,0,0)`
  have hB : Work.BoxShrink.Pinch.boxB idDiffeo tangentCtr tangentCyc3 (0, Real.pi) < tangentRad := by
    have hbox : Work.BoxShrink.Pinch.boxB idDiffeo tangentCtr tangentCyc3 (0, Real.pi) = 0 := by
      rw [Work.BoxShrink.Pinch.boxB_apply]
      show Submission.boxNorm tangentCtr tangentCyc3
        (Work.BoxShrink.Pinch.par idDiffeo (0, Real.pi)) = 0
      rw [Work.BoxShrink.Pinch.par_apply]
      simp only [idDiffeo, id_eq]
      rw [boxNorm_tangent]
      simp only [Work.CoreTopology.torusMap_apply_zero, Work.CoreTopology.torusMap_apply_one,
        Work.CoreTopology.torusMap_apply_two, Real.cos_pi, Real.cos_zero, Real.sin_zero,
        Real.sin_pi]
      norm_num
    rw [hbox]
    norm_num [tangentRad]
  have hG : Work.BoxShrink.Pinch.planeG idDiffeo tangentCtr tangentCyc3 0 (0, Real.pi) = 0 := by
    rw [planeG_idDiffeo_tangent]
    norm_num
  have hD : fderiv ℝ (Work.BoxShrink.Pinch.planeG idDiffeo tangentCtr tangentCyc3 0)
      (0, Real.pi) = 0 := by
    rw [planeG_idDiffeo_tangent, fderiv_tangent_planeG]
    simp [Real.cos_pi, Real.sin_pi, Real.sin_zero, Real.cos_zero]
  exact (h (0, Real.pi) hB hG) hD

end

end Work.BoxShrink.PinchOff
