import Mathlib
import Submission.Work.PinchFamily.Defs

/-!
# The slice is a collar of the pinch, when it is open in the surface and spans nothing

The slice `Work.PinchFamily.slice P s c σ u` is always closed in the surface and contained in the box
region.  `SpanCollarBody` asks for an open collar containing it whose winding span vanishes; the
slice itself is such a collar as soon as it happens to be **open** in the surface and to **span
nothing**:

* openness of the slice is `hopen`;
* the *complement in the box region* is `boxRegion \ sliceRegion = upperRegion ∪ lowerRegion`, the
  two half-regions, which are open in the surface
  (`Work.PinchCounted.PinchSweep.isOpenInCarrier_halves`);
* the vanishing of the winding span is `hbot`.

So the two hypotheses are exactly the two things that make the slice a `CountedStep`-piece of
vanishing span, and `SpanCollarBody` follows.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchFamily

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The complement of the slice in the box region is the two half-regions.**  The box region is
`(upperRegion ∪ lowerRegion) ∪ sliceRegion` (`Work.BoxShrink.Core.boxRegion_eq_union`), the two
half-regions meet neither the slice (their points lie strictly off the cutting plane) nor each
other. -/
theorem boxRegion_sdiff_sliceRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    box P s c σ \ slice P s c σ u = halves P s c σ u := by
  ext y
  constructor
  · rintro ⟨hybox, hyslice⟩
    obtain ⟨hyc, hyb⟩ := Work.BoxShrink.Core.mem_boxRegion.mp hybox
    have hne : y (σ 2) ≠ c (σ 2) + u := fun h =>
      hyslice (Work.BoxShrink.Core.mem_sliceRegion.mpr ⟨hyc, hyb, h⟩)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr (Work.BoxShrink.Core.mem_lowerRegion.mpr ⟨hyc, hyb, h⟩)
    · exact Or.inl (Work.BoxShrink.Core.mem_upperRegion.mpr ⟨hyc, hyb, h⟩)
  · rintro (hu | hl)
    · exact ⟨Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hu.1.1, hu.1.2⟩,
        fun h => ne_of_gt (Work.BoxShrink.Core.mem_upperHalf.mp hu.2)
          (Work.BoxShrink.Core.mem_sliceRegion.mp h).2.2⟩
    · exact ⟨Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hl.1.1, hl.1.2⟩,
        fun h => ne_of_lt (Work.BoxShrink.Core.mem_lowerHalf.mp hl.2)
          (Work.BoxShrink.Core.mem_sliceRegion.mp h).2.2⟩

/-- **An open slice of vanishing winding span is a collar of the pinch.**

Taking `Z` to be the slice itself: it contains the slice, it lies in the box region
(`Work.BoxShrink.Core.sliceRegion_subset`), it is open by hypothesis, and its complement in the box
region is the union of the two half-regions (`boxRegion_sdiff_sliceRegion`), which is open in the
surface.  The winding span is the hypothesis `hbot`. -/
theorem spanCollarBody_of_sliceRegion_open {P : Work.CoreTopology.ParamTorus}
    (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P (Work.PinchFamily.slice P s c σ u))
    (hbot : Work.SurgeryInvariance.WindingSpan P (Work.PinchFamily.slice P s c σ u) = ⊥) :
    Work.PinchFamily.SpanCollarBody P β s c σ u := by
  refine ⟨slice P s c σ u, ⟨hopen, subset_rfl,
    Work.BoxShrink.Core.sliceRegion_subset P s c σ u, ?_⟩, hbot⟩
  rw [boxRegion_sdiff_sliceRegion]
  exact Work.PinchCounted.PinchSweep.isOpenInCarrier_halves P s c σ u

end

end Work.PinchFamily
