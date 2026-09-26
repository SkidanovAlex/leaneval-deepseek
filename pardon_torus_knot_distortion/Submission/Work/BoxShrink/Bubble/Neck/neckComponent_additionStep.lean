import Mathlib
import Submission.Work.BoxShrink.Bubble.Defs
import Submission.Work.SurgeryInvariance.Loops

namespace Work.BoxShrink.Bubble.Neck

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- Auxiliary: the decomposition of `upperRegion ∪ lowerRegion` used in the addition step. -/
theorem upper_union_lower_eq_diff_union_inter {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (N : Work.BoxShrink.Bubble.NeckComponent P s c σ u) :
    (Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u) =
      (Work.BoxShrink.Core.boxRegion P s c σ \ N.C) ∪
        (N.C ∩ (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u)) := by
  rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u]
  ext y
  constructor
  · intro hy
    by_cases hyC : y ∈ N.C
    · exact Or.inr ⟨hyC, hy⟩
    · exact Or.inl ⟨Or.inl hy, hyC⟩
  · rintro (⟨hyB, hyC⟩ | ⟨hyC, hy⟩)
    · rcases hyB with h | h
      · exact h
      · exact absurd (N.slice_subset h) hyC
    · exact hy

theorem neckComponent_additionStep {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (N : Work.BoxShrink.Bubble.NeckComponent P s c σ u) :
    Work.SurgeryInvariance.SurgeryStepZero P
      (Work.BoxShrink.Core.boxRegion P s c σ \ N.C)
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  refine ⟨N.C ∩ (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u), ?_, ?_, ?_, ?_, ?_⟩
  · -- the added piece lies in the neck component, hence carries no essential loop
    have hle : Work.SurgeryInvariance.WindingSpan P
        (N.C ∩ (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u)) ≤
        Work.SurgeryInvariance.WindingSpan P N.C :=
      Work.SurgeryInvariance.WindingSpan_mono P Set.inter_subset_left
    rw [N.span] at hle
    exact le_bot_iff.mp hle
  · -- `boxRegion \ C` is closed in the region, by definition of a neck component
    exact N.closed'
  · -- the union of the two half-regions is open in the surface
    exact Work.SurgeryInvariance.isOpenInCarrier_union P
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
  · -- the added piece is an intersection of open pieces
    exact Work.SurgeryInvariance.isOpenInCarrier_inter P N.open'
      (Work.SurgeryInvariance.isOpenInCarrier_union P
        (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
        (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u))
  · refine Or.inr ⟨?_, ?_⟩
    · exact upper_union_lower_eq_diff_union_inter N
    · -- disjointness: `boxRegion \ C` lies off `C`, the added piece in `C`
      rw [Set.disjoint_left]
      intro y hyA hyZ
      exact hyA.2 hyZ.1

end Work.BoxShrink.Bubble.Neck
