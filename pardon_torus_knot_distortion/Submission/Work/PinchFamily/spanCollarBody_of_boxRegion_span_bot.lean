import Mathlib
import Submission.Work.PinchFamily.Defs

/-!
# A box region of vanishing winding span is a collar of the pinch

If the region inside the box `Work.PinchFamily.box P s c σ` has vanishing winding span, then it is
itself a collar of the pinch: taking `Z` to be the whole box region,

* `Z` is open in the surface (`Work.BoxShrink.Core.isOpenInCarrier_boxRegion`, because Pardon's box
  is open);
* `Z` contains the slice trace (`Work.BoxShrink.Core.sliceRegion_subset`) and is contained in the
  box region (trivially);
* the complement `box \ Z` is empty, hence open in the surface;
* and the winding span of `Z` is `⊥` by hypothesis.

So `SpanCollarBody` follows from `WindingSpan P (box P s c σ) = ⊥` alone.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.PinchFamily

noncomputable section

/-- **The empty set is open in the surface** (it is the complement of the whole carrier). -/
theorem isOpenInCarrier_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.IsOpenInCarrier P (∅ : Set R3) := by
  rw [Work.SurgeryInvariance.IsOpenInCarrier]
  simp

/-- **A box region of vanishing winding span is a collar of the pinch.**

Taking `Z` to be the whole box region `box P s c σ`: it is open in the surface, contains the slice
trace, is contained in itself, has empty (hence open) complement in itself, and its winding span
vanishes by hypothesis. -/
theorem spanCollarBody_of_boxRegion_span_bot {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hbot : Work.SurgeryInvariance.WindingSpan P (Work.PinchFamily.box P s c σ) = ⊥) :
    Work.PinchFamily.SpanCollarBody P β s c σ u := by
  refine ⟨box P s c σ, ⟨Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ,
    Work.BoxShrink.Core.sliceRegion_subset P s c σ u, subset_rfl, ?_⟩, hbot⟩
  rw [Set.sdiff_self]
  exact isOpenInCarrier_empty P

end

end Work.PinchFamily
