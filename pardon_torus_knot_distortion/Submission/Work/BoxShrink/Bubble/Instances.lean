import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.Instances.slicePushOff_of_empty_slice
import Submission.Work.BoxShrink.Bubble.Instances.slicePushOff_of_span_bot

/-!
# Pardon's double bubble: the cases in which the input is proved

The geometric input of the construction is `Work.BoxShrink.Bubble.SlicePushOff`: every winding
vector realised by a loop of the surface inside Pardon's box is realised by a loop away from the
slicing plane.  This file collects the cases in which it is *proved*, and the resulting
unconditional instances of Pardon's double bubble:

* `slicePushOff_of_empty_slice` (delegated): if the slicing plane misses the surface inside the box,
  the region inside the sphere already *is* the union of the two half-regions;
* `slicePushOff_of_span_bot` (delegated): if the region inside the sphere realises only the trivial
  winding vector, the push-off is immediate (the constant loop in the nonempty half-region);
* `slicePushOff_of_essential_avoids`: if every essential loop of the region already avoids the
  slicing plane, the push-off is immediate — the only loops which have to be moved are the
  inessential ones, and those may be replaced by a constant loop;
* `bubble_of_empty_slice`, `bubble_of_zero_span`: the corresponding unconditional instances of
  `Work.BoxShrink.Core.BubbleSweep` (Pardon's family for the box/plane configuration);
* `slicePushOff_iff` — the input is exactly the loop-level datum
  `Work.BoxShrink.Core.DoubleBubbleDatum`, restated for convenience.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The push-off is immediate when the essential loops of the region already avoid the plane.**
The only loops whose winding has to be transported are the inessential ones, which can be replaced
by a constant loop in the (nonempty) union of the two half-regions. -/
theorem slicePushOff_of_essential_avoids {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ) →
      ¬ Work.CoreTopology.IsEssential P γ ∨
        (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u))
    (hne : ∃ a : R3, a ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) :
    SlicePushOff P s c σ u := by
  intro k hk
  obtain ⟨γ, hγ, hkγ⟩ := hk
  rcases h γ hγ with hnil | hkeep
  · obtain ⟨a, ha⟩ := hne
    have hacarrier : a ∈ P.carrier := ha.elim (fun h => h.1.1) (fun h => h.1.1)
    have hw : Work.SurgeryInvariance.windingOf P γ = (0, 0) := by
      by_contra hc
      exact hnil ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mpr hc)
    have hw' : Work.SurgeryInvariance.windingOf P
        (Work.InnermostDisk.constCurve P a hacarrier) = (0, 0) := by
      by_contra hc
      exact Work.InnermostDisk.not_isEssential_of_const P a hacarrier
        ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P _).mpr hc)
    exact ⟨Work.InnermostDisk.constCurve P a hacarrier, fun _ => ha, by rw [hw']; exact hw.symm.trans hkγ⟩
  · exact ⟨γ, hkeep, hkγ⟩

/-- **Only the loops which meet the slicing plane matter.**  A loop of the region whose image
avoids the slice already lies in `upperRegion ∪ lowerRegion`, so the push-off is only about the
loops that meet the slice.  This is the sharpest form of the input that the construction consumes:
`SlicePushOff` is equivalent to the condition that every loop of the region meeting the slice has a
companion in `upperRegion ∪ lowerRegion` with the same winding. -/
theorem slicePushOff_of_meeting {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ) →
      (∃ t : ℝ, γ t ∈ Work.BoxShrink.Core.sliceRegion P s c σ u) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ∧
        Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ) :
    SlicePushOff P s c σ u := by
  intro k hk
  obtain ⟨γ, hγ, hkγ⟩ := hk
  by_cases hmeet : ∃ t : ℝ, γ t ∈ Work.BoxShrink.Core.sliceRegion P s c σ u
  · obtain ⟨γ', hγ', hw⟩ := h γ hγ hmeet
    exact ⟨γ', hγ', by rw [hw, hkγ]⟩
  · push_neg at hmeet
    -- the loop avoids the slice, hence lies in the union of the two half-regions
    refine ⟨γ, fun t => ?_, hkγ⟩
    have hbox : γ t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u ∪
        Work.BoxShrink.Core.sliceRegion P s c σ u := by
      rw [← Work.BoxShrink.Core.boxRegion_eq_union]
      exact hγ t
    rcases hbox with h | h
    · exact h
    · exact absurd h (hmeet t)

/-- **Pardon's family in the degenerate case in which the slicing plane misses the surface inside
the box**: the two-point family with no surgery at all. -/
noncomputable def bubble_of_empty_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅) :
    Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  bubble_of_slicePushOff (Instances.slicePushOff_of_empty_slice h)

/-- **Pardon's family when the region inside the sphere realises only the trivial winding**: the
push-off is immediate, hence so is the family. -/
noncomputable def bubble_of_zero_span {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥)
    (hne : ∃ a : R3, a ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) :
    Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  bubble_of_slicePushOff (Instances.slicePushOff_of_span_bot h hne)

/-- **The input, restated**: `SlicePushOff` is exactly the loop-level datum of Pardon's double
bubble at the pair (region inside the sphere, union of the two half-regions). -/
theorem slicePushOff_iff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    SlicePushOff P s c σ u ↔ Work.BoxShrink.Core.DoubleBubbleDatum P s c σ u :=
  (pushOffDatum_iff_slicePushOff P s c σ u).symm

end

end Work.BoxShrink.Bubble
