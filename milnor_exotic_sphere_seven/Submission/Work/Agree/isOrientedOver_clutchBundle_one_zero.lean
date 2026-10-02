import Submission.Work.Agree.crux
import Submission.Work.Agree.det_qTwist_one_zero_pos
import Submission.Work.Thom.isOrientedOver_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Orientation of `L¹R⁰ = clutchBundle 1 0` over the two-chart cover of `S⁴`

`Work.Thom.isOrientedOver_of_det_pos` produces `Work.Thom.IsOrientedOver` from a *positive
determinant* of the chart transition.  For the two-chart bundle `clutchBundle 1 0` the cover is
`hemi0 = baseSet false`, `hemi1 = baseSet true` and the transition is
`qTwist 1 0 (uDir p)`, left multiplication by the unit quaternion `uDir p`, whose determinant is
positive by `Work.Agree.det_qTwist_one_zero_pos` (itself `Work.Agree.detMulLeftPos` plus
`det_comp` along `qTwist = ofQ ∘ mulLeft ∘ toQ`).

This is the orientation input of the Thom class of `clutchBundle 1 0`, the first ingredient of
`Work.Agree.bottHopfOne`.
-/

namespace Work.Agree

open Work.TangentClasses

/-- The tangent-classes `RealBundle` model of `S⁴` (definitionally `OnePoint (EuclideanSpace ℝ (Fin 4))`). -/
abbrev S4' : Type := S4

/-- `‖uDir p‖ = 1`: `uDir` is the unit direction, unconditionally a point of the unit sphere. -/
lemma norm_uDir' (p : S4) : ‖uDir p‖ = 1 := by
  have h : uDir p ∈ Metric.sphere (0 : Quaternion ℝ) 1 :=
    (Submission.Milnor.unitDir (coord0 p)).2
  rwa [Metric.mem_sphere, dist_zero_right] at h

/-- **`clutchBundle 1 0` is oriented over the cover by the two hemispheres.** -/
theorem isOrientedOver_clutchBundle_one_zero :
    Work.Thom.IsOrientedOver (clutchBundle 1 0) 4 hemi0 hemi1 := by
  refine Work.Thom.isOrientedOver_of_det_pos (U := hemi0) (V := hemi1) (i := false) (j := true)
    4 (by norm_num) (by rw [finrank_euclideanSpace_fin]) (clutchBundle 1 0) ?_ ?_ ?_
  · intro x hx
    exact hx
  · intro x hx
    exact hx
  · intro x
    show 0 < LinearMap.det ((qTwist 1 0 (uDir (x : S4))).toLinearMap)
    exact det_qTwist_one_zero_pos (uDir (x : S4)) (norm_uDir' (x : S4))

end Work.Agree
