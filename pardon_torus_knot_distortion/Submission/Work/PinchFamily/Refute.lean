import Submission.Work.PinchFamily.Instances
import Submission.Work.PinchFamily.regionPushOff_of_localFamilyBody
import Submission.Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top
import Submission.Work.BoxShrink.Bubble.Corrected

/-!
# The local residual fails at the standard `5/2` configuration

`Instances.lean` proves that the push-off residual fails at the standard torus of revolution with
the box `s = 5/2`, `c = 0`, `σ = swap 1 2` and the plane level `u = 0`
(`Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`).  At that configuration the two half-regions
*do* carry an essential loop (the region inside the box spans everything,
`Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top`, and Pardon's conclusion holds there,
`Work.BoxShrink.Bubble.bubbleHalf_cex`), so the sharpness theorem
`Work.PinchFamily.regionPushOff_of_localFamilyBody` applies and gives:

> **there is no family of regions from the box region to the two half-regions whose local moves are
> all `CountedStep`s, at the standard `5/2` configuration.**

Consequently, if the local residual `Work.PinchFamily.PinchFamilyResidual` (= Pardon's counted
`CountedPinch`) is true, then the counting hypotheses of the crux are *unsatisfiable* at that
configuration — the same conclusion the previous chapter reaches by the different route of the
sphere-trace classification.  The residual is therefore not vacuous: it is refuted at an explicit
configuration, and it is exactly the counting that has to exclude it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchFamily

noncomputable section

/-- **The region inside the box of the standard `5/2` configuration carries an essential loop.** -/
theorem containsEssentialLoop_box_cex :
    Work.CoreTopology.standard.ContainsEssentialLoop
      (box Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2)) :=
  (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp (by
    rw [Work.BoxShrink.Bubble.cex_windingSpan_boxRegion_eq_top]
    exact top_ne_bot)

/-- **The two half-regions of the standard `5/2` configuration carry an essential loop.** -/
theorem containsEssentialLoop_halves_cex :
    Work.CoreTopology.standard.ContainsEssentialLoop
      (halves Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0) := by
  rcases Work.BoxShrink.Bubble.bubbleHalf_cex containsEssentialLoop_box_cex with h | h
  · exact ⟨h.choose, h.choose_spec.1, fun t => Or.inl (h.choose_spec.2 t)⟩
  · exact ⟨h.choose, h.choose_spec.1, fun t => Or.inr (h.choose_spec.2 t)⟩

/-- **At the standard `5/2` configuration the slice trace carries no essential loop, and yet the
push-off fails.**  So neither the vanishing of the span of the slice trace nor the two endpoint
inessentiality hypotheses imply the residual: the counting of Pardon's proof has to enter through the
*intermediate* spheres of the pinching family, not through the endpoints. -/
theorem slice_inessential_and_not_regionPushOff_cex :
    ¬ Work.CoreTopology.standard.ContainsEssentialLoop
        (slice Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0) ∧
      ¬ RegionPushOff Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 :=
  ⟨Work.BoxShrink.Bubble.cex_not_containsEssentialLoop_sliceRegion, not_regionPushOff_cex⟩

/-- **No family of `CountedStep`s joins the box region to the two half-regions at the standard
`5/2` configuration.** -/
theorem not_localFamilyBody_cex
    (β : Work.CoreTopology.ClosedCurve Work.CoreTopology.standard) :
    ¬ LocalFamilyBody Work.CoreTopology.standard β (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 :=
  fun h => not_regionPushOff_cex
    (regionPushOff_of_localFamilyBody β h containsEssentialLoop_halves_cex)

end

end Work.PinchFamily
