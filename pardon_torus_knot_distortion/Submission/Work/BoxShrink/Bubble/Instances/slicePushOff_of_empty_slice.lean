import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic

namespace Work.BoxShrink.Bubble.Instances

/-- **If the slice is empty, the push-off is trivial.**  When `sliceRegion P s c σ u = ∅` the
region inside the box is literally the union of the two half-regions
(`Work.BoxShrink.Core.boxRegion_eq_union`), so every winding vector realised inside the box is
already realised away from the slicing plane. -/
theorem slicePushOff_of_empty_slice
    {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅) :
    Work.BoxShrink.Bubble.SlicePushOff P s c σ u := by
  unfold Work.BoxShrink.Bubble.SlicePushOff
  rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u, h, Set.union_empty]

end Work.BoxShrink.Bubble.Instances
