import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.OpenSlice
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_of_surgeryStepZero

/-!
# The field and the push-off are the same statement in the nondegenerate case

The chapter delivers the field `bubble` of `Work.BoxShrink.Core.BubbleInput` from the isolated
loop-level input `Work.BoxShrink.Bubble.SlicePushOff`.  The reduction in one direction is
`Work.BoxShrink.Bubble.bubble_of_slicePushOff`; the reverse direction is
`Work.BoxShrink.Bubble.slicePushOff_of_bubbleSweep`, which *a priori* needs two side conditions on
the sweep (all its regions nonempty and contained in the surface).

This file shows that those side conditions are **automatic** as soon as the region inside the box
carries an essential loop, i.e. `WindingSpan P (boxRegion) ≠ ⊥`:

* the winding span is constant along a loop-level sweep
  (`Work.SurgeryInvariance.SweepLoops.windingSpan_eq`), so every region of the sweep has nonzero
  winding span, hence contains a loop, hence is nonempty;
* intersecting every region of the sweep with the surface `F = P.carrier` changes neither the local
  moves nor the winding spans (`windingSpan_inter_carrier`, `regionEquivalent_inter_carrier`,
  `surgeryStepZero_inter_carrier`, `sweepLoops_inter_carrier`), and gives regions contained in
  `F`;
* the endpoints of the intersected sweep are still `boxRegion` and `upperRegion ∪ lowerRegion`,
  because both are contained in `F`.

Consequently (`bubbleSweep_nonempty_iff_slicePushOff`)

  *a `BubbleSweep` exists if and only if `SlicePushOff` holds*

for every configuration whose region inside the box carries an essential loop.  So in the
nondegenerate case the isolated input of the chapter is *not* a weakening of the field: it is the
field, and any further progress on the field must be progress on the push-off.  (The degenerate
cases are treated by `Work.BoxShrink.Bubble.bubble_of_empty_slice`,
`Work.BoxShrink.Bubble.bubble_of_zero_span` and `Work.BoxShrink.Bubble.bubbleSweep_of_sliceOpen`.)

## A new case of the push-off

`slicePushOff_of_sliceOpen`: if the slice is **open in the surface**, then
`SurgeryStepZero P boxRegion (upperRegion ∪ lowerRegion)`
(`Work.BoxShrink.Bubble.surgeryStepZero_boxRegion_of_sliceOpen`) upgrades to the loop transport
(`Work.BoxShrink.Bubble.Toolkit.regionEquivalent_of_surgeryStepZero`), so `SlicePushOff` holds —
provided the two halves are nonempty.  This makes the push-off available in the one case in which
the pinch degenerates (`OpenSlice.lean`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Intersecting a region with the surface -/

/-- The winding vectors realised in `X` and in `X ∩ F` agree: a loop of the torus lies in `F`. -/
theorem windingVectors_inter_carrier (X : Set R3) :
    Work.SurgeryInvariance.windingVectors P (X ∩ P.carrier) =
      Work.SurgeryInvariance.windingVectors P X := by
  ext v
  constructor
  · rintro ⟨γ, hγ, hv⟩
    exact ⟨γ, fun t => (hγ t).1, hv⟩
  · rintro ⟨γ, hγ, hv⟩
    exact ⟨γ, fun t => ⟨hγ t, γ.mem t⟩, hv⟩

/-- The winding span is unchanged by intersecting with the surface. -/
theorem windingSpan_inter_carrier (X : Set R3) :
    Work.SurgeryInvariance.WindingSpan P (X ∩ P.carrier) =
      Work.SurgeryInvariance.WindingSpan P X := by
  rw [Work.SurgeryInvariance.WindingSpan, Work.SurgeryInvariance.WindingSpan,
    windingVectors_inter_carrier]

/-- Intersecting with the surface preserves openness in the surface. -/
theorem isOpenInCarrier_inter_carrier {X : Set R3}
    (h : Work.SurgeryInvariance.IsOpenInCarrier P X) :
    Work.SurgeryInvariance.IsOpenInCarrier P (X ∩ P.carrier) := by
  have hpre : (Subtype.val : P.carrier → R3) ⁻¹' P.carrier = Set.univ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => x.2⟩
  have : (Subtype.val : P.carrier → R3) ⁻¹' (X ∩ P.carrier) =
      (Subtype.val : P.carrier → R3) ⁻¹' X := by
    rw [Set.preimage_inter, hpre, Set.inter_univ]
  rw [Work.SurgeryInvariance.IsOpenInCarrier, this]
  exact h

/-- A loop transport survives intersecting with the surface. -/
theorem regionEquivalent_inter_carrier {X Y : Set R3}
    (h : Work.SurgeryInvariance.RegionEquivalent P X Y) :
    Work.SurgeryInvariance.RegionEquivalent P (X ∩ P.carrier) (Y ∩ P.carrier) := by
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_⟩
  · obtain ⟨γ', hγ', hw⟩ := h.1 γ (fun t => (hγ t).1)
    exact ⟨γ', fun t => ⟨hγ' t, γ'.mem t⟩, hw⟩
  · obtain ⟨γ', hγ', hw⟩ := h.2 γ (fun t => (hγ t).1)
    exact ⟨γ', fun t => ⟨hγ' t, γ'.mem t⟩, hw⟩

/-- A single `2`-surgery survives intersecting with the surface. -/
theorem surgeryStepZero_inter_carrier {X Y : Set R3}
    (h : Work.SurgeryInvariance.SurgeryStepZero P X Y) :
    Work.SurgeryInvariance.SurgeryStepZero P (X ∩ P.carrier) (Y ∩ P.carrier) := by
  obtain ⟨Z, hZ, hX, hY, hZo, hcase⟩ := h
  refine ⟨Z ∩ P.carrier, ?_, isOpenInCarrier_inter_carrier hX, isOpenInCarrier_inter_carrier hY,
    isOpenInCarrier_inter_carrier hZo, ?_⟩
  · rw [windingSpan_inter_carrier]; exact hZ
  · rcases hcase with ⟨hcover, hdisj⟩ | ⟨hcover, hdisj⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [hcover, Set.union_inter_distrib_right]
      · exact hdisj.mono Set.inter_subset_left Set.inter_subset_left
    · right
      refine ⟨?_, ?_⟩
      · rw [hcover, Set.union_inter_distrib_right]
      · exact hdisj.mono Set.inter_subset_left Set.inter_subset_left

/-- **Intersecting every region of a loop-level sweep with the surface** gives a loop-level sweep
with the same exceptional set and the same winding spans. -/
theorem exists_sweepLoops_inter_carrier (S : Work.SurgeryInvariance.SweepLoops P) :
    ∃ S' : Work.SurgeryInvariance.SweepLoops P,
      (∀ t : ℝ, S'.region t = S.region t ∩ P.carrier) ∧ S'.exc = S.exc := by
  refine ⟨⟨fun t => S.region t ∩ P.carrier, S.exc, ?_, ?_⟩, fun _ => rfl, rfl⟩
  · intro t ht
    obtain ⟨ε, hε, hno, hreg⟩ := S.regular t ht
    exact ⟨ε, hε, hno, fun s hs => regionEquivalent_inter_carrier (hreg s hs)⟩
  · intro t ht
    obtain ⟨ε, hε, hstep⟩ := S.surgery t ht
    refine ⟨ε, hε, fun s hs => ?_⟩
    rcases hstep s hs with h | h
    · exact Or.inl (surgeryStepZero_inter_carrier h)
    · exact Or.inr (regionEquivalent_inter_carrier h)

/-- The empty set has vanishing winding span. -/
theorem windingSpan_empty : Work.SurgeryInvariance.WindingSpan P (∅ : Set R3) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, -, hγ⟩
  exact (hγ 0)

/-! ## The field is the push-off in the nondegenerate case -/

/-- **The field gives the push-off as soon as the region carries an essential loop.**

If `WindingSpan P (boxRegion) ≠ ⊥` then every region of the sweep has nonzero winding span
(span constancy), hence is nonempty, and intersecting the sweep with the surface produces a sweep
whose regions are contained in the surface with the same endpoints.  This discharges the two side
conditions of `Work.BoxShrink.Bubble.slicePushOff_of_bubbleSweep`. -/
theorem slicePushOff_of_bubbleSweep_of_windingSpan_ne_bot {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (B : Work.BoxShrink.Core.BubbleSweep P s c σ u)
    (hspan : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥) :
    SlicePushOff P s c σ u := by
  obtain ⟨S', hS', -⟩ := exists_sweepLoops_inter_carrier B.sweep
  have hzero : S'.region 0 = Work.BoxShrink.Core.boxRegion P s c σ := by
    rw [hS' 0, B.zero, Set.inter_eq_left]
    exact fun x hx => hx.1
  have hone : S'.region 1 = Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u := by
    rw [hS' 1, B.one, Set.inter_eq_left]
    rintro x (hx | hx)
    · exact (Work.BoxShrink.Core.mem_upperRegion.mp hx).1
    · exact (Work.BoxShrink.Core.mem_lowerRegion.mp hx).1
  refine slicePushOff_of_bubbleSweep ⟨S', hzero, hone⟩ ?_ ?_
  · intro t
    show S'.region t ⊆ P.carrier
    rw [hS' t]
    exact Set.inter_subset_right
  intro t
  by_contra hne
  have hemp : S'.region t = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  have hbot : Work.SurgeryInvariance.WindingSpan P (S'.region t) = ⊥ := by
    rw [hemp]; exact windingSpan_empty
  have := S'.windingSpan_eq t
  rw [hzero] at this
  exact hspan (this ▸ hbot)

/-- **In the nondegenerate case the field and the push-off are the same statement.**

For every configuration whose region inside the box carries an essential loop, a `BubbleSweep`
exists if and only if `SlicePushOff` holds.  So the isolated input of the chapter is not a
weakening of the field there — a proof of the field must be a proof of the push-off. -/
theorem bubbleSweep_nonempty_iff_slicePushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hspan : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥) :
    Nonempty (Work.BoxShrink.Core.BubbleSweep P s c σ u) ↔ SlicePushOff P s c σ u :=
  ⟨fun ⟨B⟩ => slicePushOff_of_bubbleSweep_of_windingSpan_ne_bot B hspan,
    fun h => ⟨bubble_of_slicePushOff h⟩⟩

/-- **The same, restricted to the configuration of the field**: with the hypothesis
`¬ ContainsEssentialLoop (sliceRegion)` (under which the sweep is asked for), the field at a
configuration with an essential loop in the box is *equivalent* to the push-off. -/
theorem bubbleSweep_iff_slicePushOff_of_hasEss {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hspan : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥) :
    (¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
        Nonempty (Work.BoxShrink.Core.BubbleSweep P s c σ u)) ↔
      (¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
        SlicePushOff P s c σ u) := by
  constructor
  · intro h hZ
    exact (bubbleSweep_nonempty_iff_slicePushOff (P := P) hspan).mp (h hZ)
  · intro h hZ
    exact (bubbleSweep_nonempty_iff_slicePushOff (P := P) hspan).mpr (h hZ)

/-! ## A new case of the push-off: the slice open in the surface -/

/-- **The push-off when the slice is open in the surface.**  The decomposition
`boxRegion = (upperRegion ∪ lowerRegion) ∪ sliceRegion` is then a genuine `2`-surgery, hence a loop
transport, so the push-off holds as soon as the two halves are nonempty. -/
theorem slicePushOff_of_sliceOpen {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P
      (Work.BoxShrink.Core.sliceRegion P s c σ u))
    (hZ : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u))
    (hne : (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u).Nonempty) :
    SlicePushOff P s c σ u := by
  have hstep := surgeryStepZero_boxRegion_of_sliceOpen (P := P) (s := s) (c := c) (σ := σ) (u := u)
    hopen hZ
  have hboxne : (Work.BoxShrink.Core.boxRegion P s c σ).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, (Work.BoxShrink.Core.boxRegion_eq_union P s c σ u) ▸ Or.inl hx⟩
  have hRE := Toolkit.regionEquivalent_of_surgeryStepZero hstep
    (fun _ hx => hx.1)
    (fun _ hx => (hx.elim (fun h => (Work.BoxShrink.Core.mem_upperRegion.mp h).1)
      (fun h => (Work.BoxShrink.Core.mem_lowerRegion.mp h).1)))
    hboxne hne
  have hset := (Toolkit.regionEquivalent_iff_realizedWindings P _ _).mp hRE
  exact hset.le

end

end Work.BoxShrink.Bubble

namespace Work.BoxShrink.Bubble

noncomputable section

end

end Work.BoxShrink.Bubble
