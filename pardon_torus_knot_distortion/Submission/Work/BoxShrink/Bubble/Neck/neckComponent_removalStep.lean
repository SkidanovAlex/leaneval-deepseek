import Mathlib
import Submission.Work.BoxShrink.Bubble.Defs
import Submission.Work.SurgeryInvariance.Loops
import Submission.Work.BoxShrink.Core.Basic

namespace Work.BoxShrink.Bubble.Neck

/-- **Removing a neck component is a single `2`-surgery.**

The region inside the box is the disjoint union of its complement in the region and the neck,
`boxRegion = (boxRegion \ N.C) ∪ N.C`: the neck lies in the region (`N.subset`), and it is clopen
in the region (`N.open'`, `N.closed'`).  Since the neck carries no essential loop (`N.span`), the
passage `boxRegion → boxRegion \ N.C` is a `SurgeryStepZero` with removed piece `Z = N.C`. -/
theorem neckComponent_removalStep {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (N : Work.BoxShrink.Bubble.NeckComponent P s c σ u) :
    Work.SurgeryInvariance.SurgeryStepZero P (Work.BoxShrink.Core.boxRegion P s c σ)
      (Work.BoxShrink.Core.boxRegion P s c σ \ N.C) := by
  exact ⟨N.C, N.span, Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ, N.closed',
    N.open', Or.inl ⟨(Set.sdiff_union_of_subset N.subset).symm, Set.disjoint_sdiff_left⟩⟩

end Work.BoxShrink.Bubble.Neck
