import Mathlib
import Submission.Work.Smooth.Plane.Cleaning
import Submission.Work.SurgeryInvariance.All

/-!
# The consequence: a planar slice meeting the knot too rarely carries no essential loop

This file delivers the **consequence** of the planar innermost-disc chapter, i.e. the reason the
double-bubble core needs it: a convex planar slice of Pardon's box which meets the knot `β` of the
challenge in fewer than `I(F, β)` points contains **no essential loop of `F`** — its winding span
vanishes.

The argument is Pardon's counting argument, unchanged from the spherical case
(`Work.InnermostDisk.mustbeinessential_of_cleansInSphere`): if `F ∩ D` contained an essential loop,
the cleaning step `CleansInConvexPlane P D` would produce a *simple* essential loop `α'` inside `D`
bounding a disc in the complement of `F`; such a loop is an element of Pardon's set `U`, so it meets
`β` in at least `I(F, β)` points (`Work.CoreTopology.pardonsI_le`); but it lies in `D`, so it meets
`β` at most as often as `D` does, contradicting `#(β ∩ D) < I(F, β)`.

## Main results

* `windingSpan_eq_bot_of_cleansInConvexPlane` — the counting argument, in the winding-span
  vocabulary of `Work.SurgeryInvariance`;
* `not_containsEssentialLoop_of_cleansInConvexPlane` — the same in the
  `ParamTorus.ContainsEssentialLoop` vocabulary;
* `windingSpan_eq_bot_of_cleansInConvexPlane_pardonsI` — the version with the explicit constant:
  `#(β ∩ D) < min p q` in place of `#(β ∩ D) < I(F, β)`.

The application to the slice `PardonSlice s c σ u` of Pardon's box — where the count
`#(β ∩ D) < min p q` comes from the plane count of `Work.BoxSweep.exists_plane_level` — is in
`Work.Smooth.Plane.PardonSlice`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Plane

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **A convex planar region meeting the knot too rarely carries no essential loop** (Pardon's
counting argument, in the winding-span vocabulary).

If `D` is a convex planar region, `CleansInConvexPlane P D` says that every essential loop of `F`
inside `D` can be replaced by a simple essential loop inside `D` bounding a disc in the complement
of `F`; such a loop is a compressing loop, hence meets `β` in at least `I(F,β)` points; and since
it lies in `D`, `D` itself meets `β` at least that often.  So if `D` meets `β` fewer than `I(F,β)`
times, `D` contains no essential loop of `F`. -/
theorem windingSpan_eq_bot_of_cleansInConvexPlane (β : Work.CoreTopology.ClosedCurve P) (D : Set R3)
    (hclean : CleansInConvexPlane P D)
    (hDβ : Set.encard (Set.range β.γ ∩ D) < Work.CoreTopology.pardonsI P β) :
    Work.SurgeryInvariance.WindingSpan P D = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, hess, hγ⟩
  exact (Work.InnermostDisk.mustbeinessential_of_cleansInSphere P β D hclean hDβ) γ hγ hess

/-- The same in the `ContainsEssentialLoop` vocabulary. -/
theorem not_containsEssentialLoop_of_cleansInConvexPlane (β : Work.CoreTopology.ClosedCurve P)
    (D : Set R3) (hclean : CleansInConvexPlane P D)
    (hDβ : Set.encard (Set.range β.γ ∩ D) < Work.CoreTopology.pardonsI P β) :
    ¬ P.ContainsEssentialLoop D := by
  rw [← Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  exact windingSpan_eq_bot_of_cleansInConvexPlane β D hclean hDβ

/-- **The counting argument with the constant `I(F,β) = min p q` made explicit.**

For the tori of the challenge, `β` the image of the standard `(p,q)`-curve, `I(F,β) = min p q`
(`Work.CoreTopology.pardonsI_standard_mapHomeomorph`); a convex planar region meeting `β` in fewer
than `min p q` points therefore carries no essential loop. -/
theorem windingSpan_eq_bot_of_cleansInConvexPlane_pardonsI {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (D : Set R3)
    (hclean : CleansInConvexPlane
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) D)
    (hDβ : Set.encard (Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ ∩ D) < (Nat.min p q : ℕ∞)) :
    Work.SurgeryInvariance.WindingSpan
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) D = ⊥ := by
  refine windingSpan_eq_bot_of_cleansInConvexPlane
    (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
      (Work.CoreTopology.standardCurve p q)) D hclean ?_
  rw [Work.CoreTopology.pardonsI_standard_mapHomeomorph p q hp hq hc ψ.toHomeomorph]
  exact hDβ

end

end Work.Smooth.Plane
