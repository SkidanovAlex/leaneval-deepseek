import Submission.Work.PinchFamily.Family
import Submission.Work.PinchFamily.Collar
import Submission.Work.PinchFamily.CollarFamily
import Submission.Work.PinchFamily.windingSpan_box_eq_halves_of_collar
import Submission.Work.PinchFamily.spanCollarBody_of_sliceRegion_open
import Submission.Work.BoxShrink.Bubble.cex_not_slicePushOffSpan

/-!
# Instances and non-vacuity of the residuals

This module records the two things a residual of this area has to satisfy to be usable: it must be
*inhabited* in a class of configurations, and it must carry *content*.

## Non-vacuity

When the cutting plane misses the surface inside the box, the slice trace is empty, the box region
**is** the union of the two half-regions, and every residual of this area holds with `Z = ∅`:

* `box_eq_halves_of_sliceRegion_empty`;
* `regionPushOff_of_sliceRegion_empty` — the push-off is the reflexivity of `RegionEquivalent`;
* `spanCollarBody_of_sliceRegion_empty`, `neckCollarBody_of_sliceRegion_empty` — the empty collar;
* `localFamilyBody_of_sliceRegion_empty`, `exists_region_of_sliceRegion_empty` — **the family of
  `Work.PinchCounted.CountedPinch` exists at every such configuration**, hence Pardon's Lemma 3
  conclusion holds there without any appeal to the pinch.

## Content

The residuals are *not* trivial: the collar and the push-off both force the winding span of the box
region to be that of the two half-regions
(`Work.PinchFamily.windingSpan_box_eq_halves_of_collar`,
`Work.PinchFamily.windingSpan_box_eq_halves_of_regionPushOff`), and that containment **fails** at the
standard configuration `s = 5/2`, `c = 0`, `σ = swap 1 2`, `u = 0`
(`Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`).  Hence no residue of this area holds at that
configuration (`not_regionPushOff_cex`, `not_spanCollarBody_cex`): the geometric input they record is
exactly what the counting supplies there, and there is no shortcut through the two endpoint regions.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchFamily

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Empty slice -/

/-- **An empty slice trace makes the box region the union of the two half-regions.** -/
theorem box_eq_halves_of_sliceRegion_empty {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : slice P s c σ u = ∅) : box P s c σ = halves P s c σ u := by
  have h' : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅ := h
  rw [box, halves, Work.BoxShrink.Core.boxRegion_eq_union P s c σ u, h', Set.union_empty]

/-- **The push-off holds trivially at an empty slice**: the two regions are equal. -/
theorem regionPushOff_of_sliceRegion_empty {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : slice P s c σ u = ∅) : RegionPushOff P s c σ u := by
  rw [RegionPushOff, box_eq_halves_of_sliceRegion_empty (P := P) h]
  exact Work.SurgeryInvariance.RegionEquivalent.refl (P := P) _

/-- **The empty collar is a collar at an empty slice**, and it has vanishing winding span. -/
theorem spanCollarBody_of_sliceRegion_empty (β : Work.CoreTopology.ClosedCurve P) {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : slice P s c σ u = ∅) :
    SpanCollarBody P β s c σ u :=
  ⟨∅, ⟨Work.BoxShrink.Pinch.isOpenInCarrier_empty P, by rw [h],
      Set.empty_subset _, by rw [Set.sdiff_empty]; exact
        Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ⟩,
    Work.BoxShrink.Pinch.windingSpan_empty P⟩

/-- **The empty collar, in matched form**, at an empty slice, given a clean low-count sphere.  The
sphere is what the counting of the crux supplies (`exists_clean_lowCount_sphere`); the matching
condition is vacuous because the empty set carries no loop. -/
theorem neckCollarBody_of_sliceRegion_empty (β : Work.CoreTopology.ClosedCurve P) {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : slice P s c σ u = ∅)
    (hS : ∃ S : Set R3, Work.InnermostDisk.CleansInSphere P S ∧
      Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β) :
    NeckCollarBody P β s c σ u := by
  obtain ⟨S, hclean, hcount⟩ := hS
  refine ⟨∅, S, ⟨Work.BoxShrink.Pinch.isOpenInCarrier_empty P, by rw [h],
    Set.empty_subset _, by rw [Set.sdiff_empty]; exact
      Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ⟩, hclean, hcount, ?_⟩
  intro γ hγ
  exact absurd (hγ 0) (by simp)

/-- **The family of Pardon's counted Lemma 3 exists at every configuration with empty slice trace**:
Pardon's pinch is a transport of the loop content, which is trivial here. -/
theorem localFamilyBody_of_sliceRegion_empty (β : Work.CoreTopology.ClosedCurve P) {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : slice P s c σ u = ∅) :
    LocalFamilyBody P β s c σ u :=
  exists_region_of_regionPushOff β (regionPushOff_of_sliceRegion_empty (P := P) h)

/-- The family of Pardon's counted Lemma 3 with the empty slice trace, displayed. -/
theorem exists_region_of_sliceRegion_empty (β : Work.CoreTopology.ClosedCurve P) {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : slice P s c σ u = ∅) :
    ∃ region : ℝ → Set R3,
      region 0 = box P s c σ ∧
      (∃ Z : Set R3, Work.SurgeryInvariance.IsOpenInCarrier P Z ∧
        Work.SurgeryInvariance.WindingSpan P Z = ⊥ ∧
        Disjoint (halves P s c σ u) Z ∧ region 1 = halves P s c σ u ∪ Z) ∧
      ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - t| < ε →
        Work.PinchCounted.CountedStep P β (region t) (region r) :=
  localFamilyBody_of_sliceRegion_empty β h

/-- **The family exists when the slice trace is open in the surface and carries no essential
loop.**  (The slice itself is then a collar with vanishing span.) -/
theorem localFamilyBody_of_openSlice_inessentialSlice (β : Work.CoreTopology.ClosedCurve P)
    {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hopen : Work.SurgeryInvariance.IsOpenInCarrier P (slice P s c σ u))
    (hbot : ¬ P.ContainsEssentialLoop (slice P s c σ u)) : LocalFamilyBody P β s c σ u :=
  localFamilyBody_of_spanCollarBody β
    (spanCollarBody_of_sliceRegion_open β hopen
      ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff P _).mpr hbot))

/-! ## The residuals imply the span containment of Pardon's Lemma 3 -/

/-- **The push-off forces the span equality.** -/
theorem windingSpan_box_eq_halves_of_regionPushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} (h : RegionPushOff P s c σ u) :
    Work.SurgeryInvariance.WindingSpan P (box P s c σ) =
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) :=
  (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq h).symm

/-! ## The residuals have content: they fail at the standard `5/2` configuration -/

/-- **The push-off fails at the configuration `s = 5/2`, `c = 0`, `σ = swap 1 2`, `u = 0` of the
standard torus.**  A push-off would force `W(boxRegion) ≤ W(halves)`, which the sibling chapter
refutes there (`Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`).  So the push-off is a genuine
geometric statement, not a consequence of the definitions: it is exactly the slice push-off that the
counting of Pardon's proof supplies (and which is *false* without it). -/
theorem not_regionPushOff_cex :
    ¬ RegionPushOff Work.CoreTopology.standard (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 :=
  fun h => Work.BoxShrink.Bubble.cex_not_slicePushOffSpan
    (le_of_eq (windingSpan_box_eq_halves_of_regionPushOff h))

/-- **The collar residual fails at the same configuration**: a collar of vanishing span would force
the span equality, hence the containment. -/
theorem not_spanCollarBody_cex (β : Work.CoreTopology.ClosedCurve Work.CoreTopology.standard) :
    ¬ SpanCollarBody Work.CoreTopology.standard β (5 / 2) 0 (Equiv.swap (1 : Fin 3) 2) 0 := by
  rintro ⟨Z, hZ, hspan⟩
  exact Work.BoxShrink.Bubble.cex_not_slicePushOffSpan
    (le_of_eq (windingSpan_box_eq_halves_of_collar (P := Work.CoreTopology.standard)
      (s := 5 / 2) (c := 0) (σ := Equiv.swap (1 : Fin 3) 2) (u := 0) hZ hspan))

end

end Work.PinchFamily
