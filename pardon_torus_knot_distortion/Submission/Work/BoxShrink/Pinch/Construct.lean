import Submission.Work.BoxShrink.Pinch.Defs
import Submission.Work.BoxShrink.Bubble.Plane.FiniteSlice
import Submission.Work.BoxShrink.Bubble.Plane.CountableSlice

/-!
# The pinch: constructing the family

The residual input of the chapter is the *construction* of Pardon's pinching family.  This module
carries out that construction in the one nondegenerate family of configurations in which the parent
chapter `Work.BoxShrink.Bubble` already knows that the loops of the region can be moved off the
slicing plane: **the box contains the whole surface and the plane meets it in finitely (or
countably) many points**.

In that situation the pinch has a very simple shape: the region does not change at all until the
last parameter, where the pinch removes the (finite, or countable) trace of the plane from the
surface.  The local model at that parameter is the *region equivalence* itself — the push-off
`Work.BoxShrink.Bubble.slicePushOff_of_finite_slice` (resp. `…_of_countable_slice`) of the parent
chapter — and the endgame is the transport of the loops of the region to the union of the halves.

The general construction (the trace of the plane is a finite union of arcs) is the remaining open
problem of the chapter; see `README.md`.

* `pinchFamilyOfRegionEquivalent` — the construction from the region equivalence alone (so it
  applies to every configuration in which the parent chapter's push-off of the loops is available);
* `pinchFamilyOfFiniteSliceOfCarrierSubset`, `pinchFamilyOfCountableSliceOfCarrierSubset`,
  `pinchFamilyOfEmptySliceOfCarrierSubset` — the instances.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- The candidate region of the construction: the region inside the box at every parameter except
the pinching parameter `1`, where it is the union of the two half-regions. -/
noncomputable def pinchRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : ℝ → Set R3 := by
  classical
  exact fun t => if t = 1 then Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u
    else Work.BoxShrink.Core.boxRegion P s c σ

theorem pinchRegion_apply {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (t : ℝ) :
    pinchRegion P s c σ u t = if t = 1 then
      Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u
      else Work.BoxShrink.Core.boxRegion P s c σ := rfl

theorem pinchRegion_of_ne {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {t : ℝ} (ht : t ≠ 1) :
    pinchRegion P s c σ u t = Work.BoxShrink.Core.boxRegion P s c σ := by
  rw [pinchRegion_apply, if_neg ht]

theorem pinchRegion_one {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    pinchRegion P s c σ u 1 = Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u := by
  rw [pinchRegion_apply, if_pos rfl]

/-- **A pinch from a region equivalence.**  Suppose the box contains the whole surface (so the
region inside the box is the surface, whose winding span is the whole of `H₁(F;ℚ)`, and Pardon's
dichotomy holds there) and that the union of the two half-regions carries the same loops as the
region inside the box.  Then Pardon's pinch exists:

* the region is the whole of the region inside the box at every parameter except `1` (`regular` and
  `surgery` are then trivial, except at `1`);
* at the last parameter the region pinches: the local model is the region equivalence itself, which
  says exactly that the loops of the box region are transported to the union of the halves;
* the endgame is that transport (`RegionEquivalent` gives, for every loop of the box region, a loop
  of the union of the halves with the same winding vector).

The piece `Z` through which the pinch passes is empty, i.e. the endpoint is Pardon's exact double
bubble. -/
theorem pinchFamilyOfRegionEquivalentOfDichotomy {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ))
    (hequiv : Work.SurgeryInvariance.RegionEquivalent P
      (Work.BoxShrink.Core.boxRegion P s c σ)
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u)) :
    Nonempty (PinchFamily P s c σ u) := by
  classical
  obtain ⟨heq₁, heq₂⟩ := hequiv
  have hreg0 : pinchRegion P s c σ u 0 = Work.BoxShrink.Core.boxRegion P s c σ :=
    pinchRegion_of_ne (by norm_num : (0 : ℝ) ≠ 1)
  have hreg1 : pinchRegion P s c σ u 1 = Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u := pinchRegion_one
  have hend : P.ContainsEssentialLoop (pinchRegion P s c σ u 0) →
      P.ContainsEssentialLoop (pinchRegion P s c σ u 1) := by
    rw [hreg0, hreg1]
    intro h
    obtain ⟨γ, hess, hγ⟩ := h
    obtain ⟨γ', hγ', hw⟩ := heq₁ γ hγ
    exact ⟨γ', (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ').mpr
      (by rw [hw]
          exact (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mp hess), hγ'⟩
  let D : PinchFamily P s c σ u :=
    { sweep :=
        { region := pinchRegion P s c σ u
          exc := {1}
          regular := by
            intro t ht
            have ht1 : t ≠ 1 := by simpa using ht
            have hpos : 0 < |t - 1| := abs_pos.mpr (sub_ne_zero.mpr ht1)
            refine ⟨|t - 1|, hpos, ?_, ?_⟩
            · intro s hs
              simp only [Finset.mem_singleton]
              intro hs1
              rw [hs1, abs_sub_comm] at hs
              exact absurd hs (lt_irrefl _)
            · intro s hs
              have hs1 : s ≠ 1 := by
                intro hs1
                rw [hs1, abs_sub_comm] at hs
                exact absurd hs (lt_irrefl _)
              rw [pinchRegion_of_ne ht1, pinchRegion_of_ne hs1]
              exact Work.SurgeryInvariance.RegionEquivalent.refl _
          surgery := by
            intro t ht
            have ht1 : t = 1 := by simpa using ht
            subst ht1
            refine ⟨1, one_pos, fun s _ => ?_⟩
            by_cases hs1 : s = 1
            · exact Or.inr (by rw [hs1]; exact Work.SurgeryInvariance.RegionEquivalent.refl _)
            · refine Or.inr ?_
              rw [pinchRegion_one, pinchRegion_of_ne hs1]
              exact ⟨heq₂, heq₁⟩
          dichotomy := by
            intro t ht
            have ht1 : t ≠ 1 := by
              intro h; rw [h] at ht; norm_num at ht
            show Work.SurgeryInvariance.WindingSpan P (pinchRegion P s c σ u t) = ⊥ ∨
              Work.SurgeryInvariance.WindingSpan P (pinchRegion P s c σ u t) = ⊤
            rw [pinchRegion_of_ne ht1]
            exact hdich }
      zero := hreg0
      Z := ∅
      Z_open := isOpenInCarrier_empty P
      Z_span := windingSpan_empty P
      Z_disj := by simp
      one := by
        change pinchRegion P s c σ u 1 = Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u ∪ ∅
        rw [hreg1, Set.union_empty]
      endgame := ⟨0, by norm_num, hend⟩ }
  exact ⟨D⟩

/-- **A pinch from a region equivalence.**  Same as `pinchFamilyOfRegionEquivalentOfDichotomy`,
with the dichotomy deduced from the box containing the whole surface (then the region inside it is
the surface itself, whose winding span is `⊤`). -/
theorem pinchFamilyOfRegionEquivalent {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hcarrier : P.carrier ⊆ Submission.PBox s c σ)
    (hequiv : Work.SurgeryInvariance.RegionEquivalent P
      (Work.BoxShrink.Core.boxRegion P s c σ)
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u)) :
    Nonempty (PinchFamily P s c σ u) := by
  have hbox : Work.BoxShrink.Core.boxRegion P s c σ = P.carrier :=
    Set.inter_eq_left.mpr hcarrier
  refine pinchFamilyOfRegionEquivalentOfDichotomy ?_ hequiv
  show Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥ ∨
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊤
  rw [hbox]
  exact Or.inr (Work.SurgeryInvariance.WindingSpan.carrier_eq_top P)

/-- **A pinch from the push-off of the loops of the region inside the box.**  This is the general
construction of this module: if Pardon's dichotomy holds at the region inside the box — i.e. its
winding span is `⊥` or `⊤`, which is what the counting supplies — and the loops of that region can
be transported off the slicing plane (`Work.BoxShrink.Bubble.SlicePushOff`, the push-off proved in
the parent chapter for a plane meeting the surface in finitely or countably many points, and in the
plateau and disc-route configurations), then Pardon's pinch exists.

The family is the simplest possible one: the region does not change until the last parameter, where
it is pinched off the plane.  The local model at that parameter is the push-off itself, expressed as
a region equivalence, and the endgame is the transport of the loops. -/
theorem pinchFamilyOfSlicePushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ))
    (h : Work.BoxShrink.Bubble.SlicePushOff P s c σ u) :
    Nonempty (PinchFamily P s c σ u) :=
  pinchFamilyOfRegionEquivalentOfDichotomy hdich
    ((Work.BoxShrink.Bubble.Toolkit.regionEquivalent_iff_realizedWindings P _ _).mpr
      (Set.Subset.antisymm h
        (Work.BoxShrink.Bubble.realizedWindings_upper_union_lower_subset P s c σ u)))

/-- **The pinch when the plane meets the region inside the box in finitely many points**, with
Pardon's dichotomy at the initial sphere as the (counting-supplied) input. -/
theorem pinchFamilyOfFiniteSlice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ))
    (hfin : (Work.BoxShrink.Core.sliceRegion P s c σ u).Finite) :
    Nonempty (PinchFamily P s c σ u) :=
  pinchFamilyOfSlicePushOff hdich
    (Work.BoxShrink.Bubble.slicePushOff_of_finite_slice (P := P) hfin)

/-- **The pinch when the plane meets the region inside the box in countably many points on
compacta**, with Pardon's dichotomy at the initial sphere as the input. -/
theorem pinchFamilyOfCountableSlice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ))
    (hcount : (Work.BoxShrink.Core.sliceRegion P s c σ u).Countable) :
    Nonempty (PinchFamily P s c σ u) :=
  pinchFamilyOfSlicePushOff hdich
    (Work.BoxShrink.Bubble.slicePushOff_of_countable_slice (P := P) hcount)

/-- **The pinch when the box contains the whole surface and the plane meets it in finitely many
points** (e.g. a plane tangent to the torus, or disjoint from it).  The region equivalence is the
push-off of the parent chapter, `Work.BoxShrink.Bubble.slicePushOff_of_finite_slice`. -/
theorem pinchFamilyOfFiniteSliceOfCarrierSubset {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hcarrier : P.carrier ⊆ Submission.PBox s c σ)
    (hfin : (Work.BoxShrink.Core.sliceRegion P s c σ u).Finite) :
    Nonempty (PinchFamily P s c σ u) :=
  pinchFamilyOfRegionEquivalent hcarrier
    ((Work.BoxShrink.Bubble.Toolkit.regionEquivalent_iff_realizedWindings P _ _).mpr
      (Set.Subset.antisymm
        (Work.BoxShrink.Bubble.slicePushOff_of_finite_slice (P := P) hfin)
        (Work.BoxShrink.Bubble.realizedWindings_upper_union_lower_subset P s c σ u)))

/-- **The pinch when the box contains the whole surface and the plane meets it in countably many
points on compacta.**  The region equivalence is
`Work.BoxShrink.Bubble.slicePushOff_of_countable_slice`. -/
theorem pinchFamilyOfCountableSliceOfCarrierSubset {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hcarrier : P.carrier ⊆ Submission.PBox s c σ)
    (hcount : (Work.BoxShrink.Core.sliceRegion P s c σ u).Countable) :
    Nonempty (PinchFamily P s c σ u) :=
  pinchFamilyOfRegionEquivalent hcarrier
    ((Work.BoxShrink.Bubble.Toolkit.regionEquivalent_iff_realizedWindings P _ _).mpr
      (Set.Subset.antisymm
        (Work.BoxShrink.Bubble.slicePushOff_of_countable_slice (P := P) hcount)
        (Work.BoxShrink.Bubble.realizedWindings_upper_union_lower_subset P s c σ u)))

/-- **The degenerate case of the construction: the plane misses the region inside the box.**  Then
the region inside the box *is* the union of the two halves and the region equivalence is the
reflexivity of the equality of the two sets. -/
theorem pinchFamilyOfEmptySliceOfCarrierSubset {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hcarrier : P.carrier ⊆ Submission.PBox s c σ)
    (hslice : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅) :
    Nonempty (PinchFamily P s c σ u) :=
  pinchFamilyOfRegionEquivalent hcarrier
    (by
      have hbox := Work.BoxShrink.Core.boxRegion_eq_union P s c σ u
      rw [hslice, Set.union_empty] at hbox
      rw [hbox]
      exact Work.SurgeryInvariance.RegionEquivalent.refl _)

end

end Work.BoxShrink.Pinch
