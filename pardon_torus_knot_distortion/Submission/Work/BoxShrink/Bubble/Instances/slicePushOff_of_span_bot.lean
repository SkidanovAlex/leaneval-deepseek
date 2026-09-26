import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic
import Submission.Work.BoxShrink.Bubble.Toolkit.windingOf_eq_zero_of_span_bot
import Submission.Work.InnermostDisk.not_isEssential_of_const

namespace Work.BoxShrink.Bubble.Instances

open LeanEval.KnotTheory.PardonDistortion

/-- **The zero winding vector is realised by every nonempty region of the surface.**

The constant closed curve at a point `x ∈ X ∩ F` has image contained in `X` and vanishes in
`H₁` (`Work.InnermostDisk.not_isEssential_of_const`), hence realises the winding vector `0`.
This is the trivial direction of `RealizedWindings`: it is what makes the geometric input
`SlicePushOff` provable as soon as the target region is nonempty. -/
theorem zero_mem_realizedWindings {P : Work.CoreTopology.ParamTorus} {X : Set R3} {x : R3}
    (hx : x ∈ X) (hxc : x ∈ P.carrier) :
    (0, 0) ∈ Work.BoxShrink.Bubble.RealizedWindings P X := by
  refine ⟨Work.InnermostDisk.constCurve P x hxc, (fun _ => hx), ?_⟩
  by_contra h
  exact Work.InnermostDisk.not_isEssential_of_const P x hxc
    ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P _).mpr h)

theorem slicePushOff_of_span_bot
    {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥)
    (hne : ∃ a : LeanEval.KnotTheory.PardonDistortion.R3,
      a ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) :
    Work.BoxShrink.Bubble.SlicePushOff P s c σ u := by
  intro k hk
  rw [Work.BoxShrink.Bubble.mem_realizedWindings] at hk
  obtain ⟨γ, hγ, hk⟩ := hk
  have hzero : Work.SurgeryInvariance.windingOf P γ = (0, 0) :=
    Work.BoxShrink.Bubble.Toolkit.windingOf_eq_zero_of_span_bot h hγ
  have hk0 : k = (0, 0) := by rw [← hk, hzero]
  rw [hk0]
  obtain ⟨a, ha⟩ := hne
  have hac : a ∈ P.carrier := by
    rcases ha with ha | ha
    · exact (Work.BoxShrink.Core.mem_upperRegion.mp ha).1
    · exact (Work.BoxShrink.Core.mem_lowerRegion.mp ha).1
  exact zero_mem_realizedWindings ha hac

end Work.BoxShrink.Bubble.Instances
