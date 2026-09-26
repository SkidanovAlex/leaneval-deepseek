import Submission.Work.BoxShrink.Bubble.Basic
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_iff_realizedWindings
import Submission.Work.BoxShrink.Bubble.Sweep.regionEquivalent_endpoints

/-!
# Pardon's double bubble for the box/plane configuration: the reduction

This is the heart of the chapter.  It reduces the field `bubble` of
`Work.BoxShrink.Core.BubbleInput` — Pardon's double bubble for the box/plane configuration — to the
single geometric statement `Work.BoxShrink.Bubble.SlicePushOff`: **every winding vector realised by
a loop of the surface inside Pardon's box is realised by a loop away from the slicing plane.**

The reduction has three steps, all proved here:

* `pushOffDatum_iff_slicePushOff`: the loop-level datum
  `Work.BoxShrink.Core.DoubleBubbleDatum P s c σ u` (i.e. `RegionEquivalent` between the region
  inside the sphere and the union of the two half-regions) is *exactly* `SlicePushOff`; the
  reverse transport (`upperRegion ∪ lowerRegion ⊆ boxRegion`) is free, so all the content of the
  double bubble at the level of loops is the push-off;
* `bubbleSweep_of_pushOffDatum`: the datum gives Pardon's family
  `Work.BoxShrink.Core.BubbleSweep P s c σ u` (`Work.BoxShrink.Core.bubbleSweep_of_doubleBubbleDatum`
  of the sibling module, which exhibits the two-point family whose only exceptional parameter is
  the transport itself);
* `bubble_of_slicePushOff` / `bubble_of_pushOffAll`: hence Pardon's double bubble for the box/plane
  configuration, in the exact shape of the field `BubbleInput.bubble`.

The geometric content of `SlicePushOff` is documented in `Work.BoxShrink.Bubble.Defs`, and the
cases in which it is *proved* here are collected in `Instances.lean`; `Obstruction.lean` records
why no construction of the family by `2`-surgeries alone can work (a `SurgeryStepZero` can only
remove a piece which is open in the surface, and the slice inside the box has no open
neighbourhood contained in the slice).
**WARNING (stretch 17).**  The isolated input `Work.BoxShrink.Bubble.SlicePushOff` consumed by all
of the theorems below is **FALSE** in general (`Work.BoxShrink.Bubble.cex_not_slicePushOff`): the
reductions here are correct, but they reduce the field to a statement which does not hold.  The
corrected interface is in `Corrected.lean` (`BubbleHalf`; and `crux_of_pushOffHalf` /
`crux_of_smoothHalf` for the crux), together with Pardon's own local model
(`PardonLocalModel.lean`, `PinchDatum` / `PardonPinchInput`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The two forms of the input -/

/-- The union of the two half-regions is contained in the region inside the sphere. -/
theorem upper_union_lower_subset_boxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u ⊆
      Work.BoxShrink.Core.boxRegion P s c σ :=
  fun y hy => (Work.BoxShrink.Core.boxRegion_eq_union P s c σ u) ▸ Or.inl hy

/-- The "free" half of the loop transport: every loop of the union of the two half-regions is a
loop of the region inside the sphere. -/
theorem realizedWindings_upper_union_lower_subset (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    RealizedWindings P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ⊆
      RealizedWindings P (Work.BoxShrink.Core.boxRegion P s c σ) :=
  RealizedWindings_mono (upper_union_lower_subset_boxRegion P s c σ u)

/-- **The datum gives the push-off**: the loop-level form of Pardon's double bubble contains the
push-off of the loops of the region off the slicing plane. -/
theorem slicePushOff_of_pushOffDatum {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : PushOffDatum P s c σ u) : SlicePushOff P s c σ u := by
  have hre : Work.SurgeryInvariance.RegionEquivalent P
      (Work.BoxShrink.Core.boxRegion P s c σ)
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) := h
  have hset := (Toolkit.regionEquivalent_iff_realizedWindings P _ _).mp hre
  exact hset.le

/-- **The push-off gives the datum**: conversely, once the loops of the region inside the sphere
are transported off the slicing plane, the region inside the sphere and the union of the two
half-regions carry the same loops with the same winding vectors (the reverse transport being
`upper_union_lower_subset_boxRegion`). -/
theorem pushOffDatum_of_slicePushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : SlicePushOff P s c σ u) : PushOffDatum P s c σ u := by
  have hset : RealizedWindings P (Work.BoxShrink.Core.boxRegion P s c σ) =
      RealizedWindings P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) :=
    Set.Subset.antisymm h (realizedWindings_upper_union_lower_subset P s c σ u)
  exact (Toolkit.regionEquivalent_iff_realizedWindings P _ _).mpr hset

/-- **The two forms of the input are the same statement.** -/
theorem pushOffDatum_iff_slicePushOff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    PushOffDatum P s c σ u ↔ SlicePushOff P s c σ u :=
  ⟨slicePushOff_of_pushOffDatum, pushOffDatum_of_slicePushOff⟩

/-! ## The span-level consequence -/

/-- The push-off gives the containment of the winding spans which Pardon's persistence argument
uses (the reverse containment is automatic). -/
theorem windingSpan_le_of_slicePushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : SlicePushOff P s c σ u) : SlicePushOffSpan P s c σ u :=
  (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq
    (pushOffDatum_of_slicePushOff h)).le

/-- **Pardon's Lemma 3 from the *span-level* input.**  The containment of the winding spans (the
weakest form of the input, see `SlicePushOffSpan`) already gives the conclusion the shrinking step
consumes: the union of the two half-regions is the disjoint union of two pieces open in the surface,
so its winding span is the supremum of theirs, whence a nonzero span of the region inside the box
forces one of the two pieces to have nonzero span. -/
theorem containsEssentialLoop_half_of_slicePushOffSpan {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : SlicePushOffSpan P s c σ u)
    (hbox : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ)) :
    P.ContainsEssentialLoop (Work.BoxShrink.Core.upperRegion P s c σ u) ∨
      P.ContainsEssentialLoop (Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  have hsplit := Work.SurgeryInvariance.Span.union_eq_sup (P := P)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)
  have hle : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
        Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) := by
    rw [← hsplit]
    exact h
  have hne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hbox
  have hsup : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ :=
    fun hbot => hne (le_bot_iff.mp (hle.trans (le_of_eq hbot)))
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ =>
    hsup (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo)

/-! ## Pardon's family -/

/-- **The double-bubble family from the datum**: Pardon's `BubbleSweep` for the box/plane
configuration, given the loop transport between the region inside the sphere and the union of the
two half-regions. -/
noncomputable def bubbleSweep_of_pushOffDatum {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : PushOffDatum P s c σ u) : Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  Classical.choice (Work.BoxShrink.Core.bubbleSweep_of_doubleBubbleDatum s c σ u h)

/-- **Pardon's double bubble for the box/plane configuration, from the push-off.**  This is the
field `bubble` of `Work.BoxShrink.Core.BubbleInput` in the form in which the chapter proves it:
the two cut hypotheses are not needed at this point, all the geometric content has been isolated in
`SlicePushOff`. -/
noncomputable def bubble_of_slicePushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : SlicePushOff P s c σ u) : Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  bubbleSweep_of_pushOffDatum (pushOffDatum_of_slicePushOff h)

/-- **The field `bubble` of `Work.BoxShrink.Core.BubbleInput`**, reduced to the push-off for every
configuration whose slicing plane carries no essential loop.

A caller who can discharge the hypothesis `h` for the tori and boxes of the challenge obtains the
required field; `Work.BoxShrink.Bubble.Instances` proves `h` in the cases where the region inside
the box or the slice is degenerate. -/
noncomputable def bubble_of_pushOffAll
    (h : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      SlicePushOff P s c σ u) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  fun _ _ _ _ _ _ hZ => bubble_of_slicePushOff (h _ _ _ _ _ hZ)

/-- **The input is exactly the loop content of Pardon's family.**  Conversely to
`bubble_of_slicePushOff`: a `BubbleSweep` whose regions are nonempty and lie in the surface gives
the push-off (chain the local moves of the family from time `0` to time `1`,
`Work.BoxShrink.Bubble.Sweep.regionEquivalent_endpoints`).  So `SlicePushOff` is not an artefact of
the way the reduction is stated: it is the loop-level content of any `SweepLoops` between the two
regions. -/
theorem slicePushOff_of_bubbleSweep {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (B : Work.BoxShrink.Core.BubbleSweep P s c σ u)
    (hcarrier : ∀ t : ℝ, B.sweep.region t ⊆ P.carrier)
    (hne : ∀ t : ℝ, (B.sweep.region t).Nonempty) :
    SlicePushOff P s c σ u := by
  have hre : Work.SurgeryInvariance.RegionEquivalent P (B.sweep.region 0) (B.sweep.region 1) :=
    Sweep.regionEquivalent_endpoints B.sweep hcarrier hne
  rw [B.zero, B.one] at hre
  exact slicePushOff_of_pushOffDatum hre

/-- **Pardon's Lemma 3 in the form the shrinking step consumes it**, from the push-off: if the
region of the surface inside the sphere contains an essential loop then so does one of the two
half-regions cut out by the plane. -/
theorem containsEssentialLoop_half_of_slicePushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} (h : SlicePushOff P s c σ u)
    (hbox : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ)) :
    P.ContainsEssentialLoop (Work.BoxShrink.Core.upperRegion P s c σ u) ∨
      P.ContainsEssentialLoop (Work.BoxShrink.Core.lowerRegion P s c σ u) :=
  Work.BoxShrink.Core.containsEssentialLoop_half_of_bubbleSweep (bubble_of_slicePushOff h) hbox

end

end Work.BoxShrink.Bubble
