import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.Obstruction.boxRegion_subset_of_surgeryStepZero
import Submission.Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty

/-!
# Why the double bubble cannot be built from `2`-surgeries alone

The local model of a single `2`-surgery of the library is

`Work.SurgeryInvariance.SurgeryStepZero P A A'`:
there is an open piece `Z` of the surface with vanishing winding span such that
`A = A' ∪ Z` (disjoint) or `A' = A ∪ Z` (disjoint), *and all three of `A`, `A'`, `Z` are open in
the surface*.

That openness is not a technicality: it forces the two regions to differ by a piece which is
**clopen** in the larger one.  Concretely, in the case `A = A' ⊔ Z` with `A`, `A'`, `Z` open, the
piece `Z` is open in the surface and its complement in `A` is `A'`, which is again open; so every
point of `Z` has a neighbourhood (in the surface) meeting `A` only inside `Z`
(`exists_open_inter_subset_of_removed`).

The slice `sliceRegion P s c σ u = F ∩ PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}` is a **closed**
subset of the region with empty interior in the surface, so it is exactly *not* of this form: at a
point of the slice the surface is locally a disc cut by an arc, and every neighbourhood meets
`upperRegion ∪ lowerRegion`.  Consequently:

* `boxRegion_subset_of_surgeryStepZero_allCases`: a single `SurgeryStepZero` whose source is the
  region inside the box and whose target contains both half-regions must have target *equal* to
  the region inside the box: it changed nothing;
* `inter_removed_eq_empty`: the piece removed by such a surgery meets the region inside the box in
  nothing.

So a `Work.SurgeryInvariance.SweepLoops` from `boxRegion` to `upperRegion ∪ lowerRegion` cannot
consist of `2`-surgeries only (the slice is never removed by one), and it cannot consist of
`RegionEquivalent` steps only either (a `RegionEquivalent` step between a region containing the
slice and one avoiding it *is* the statement `SlicePushOff`, the input of this chapter).  That is
exactly why the input `Work.BoxShrink.Bubble.SlicePushOff` is the honest content of the double
bubble in this vocabulary.

**Caveat.**  The two results above assume `SliceLocallyTwoSided`, i.e. that the surface is locally
`2`-dimensional at a point of the slicing plane: a `Work.CoreTopology.ParamTorus` is only assumed
to be continuous, so the local flatness of `F` at a point of the plane is recorded as a hypothesis
rather than proved here.  The point of the results is the obstruction, not the hypothesis.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The removed piece of a `SurgeryStepZero` is clopen in the region**: every point of it has a
neighbourhood in `ℝ³` whose trace on the region lies in the piece. -/
theorem exists_open_inter_subset_of_removed {A Z : Set R3} (hAc : A ⊆ P.carrier)
    (hZ : Work.SurgeryInvariance.IsOpenInCarrier P Z) :
    ∀ x ∈ Z, x ∈ A → ∃ U : Set R3, IsOpen U ∧ x ∈ U ∧ U ∩ A ⊆ Z := by
  intro x hxZ hxA
  have hxc : x ∈ P.carrier := hAc hxA
  obtain ⟨V, hVopen, hV⟩ := isOpen_induced_iff.mp hZ
  have hxV : x ∈ V := by
    have : (⟨x, hxc⟩ : ↥P.carrier) ∈ Subtype.val ⁻¹' V := by
      rw [hV]
      exact hxZ
    exact this
  refine ⟨V, hVopen, hxV, ?_⟩
  intro y hy
  have hyc : y ∈ P.carrier := hAc hy.2
  have : (⟨y, hyc⟩ : ↥P.carrier) ∈ Subtype.val ⁻¹' Z := by
    rw [← hV]
    exact hy.1
  exact this

/-- **No single `2`-surgery removes any point of the slice.**  If a `SurgeryStepZero` starts at the
region inside the box and ends at a region containing both half-regions, then it ends at the
region inside the box itself. -/
theorem boxRegion_subset_of_surgeryStepZero_allCases {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (htwo : SliceLocallyTwoSided P s c σ u)
    {A' : Set R3}
    (h : Work.SurgeryInvariance.SurgeryStepZero P
      (Work.BoxShrink.Core.boxRegion P s c σ) A')
    (hupper : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ A')
    (hlower : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ A') :
    Work.BoxShrink.Core.boxRegion P s c σ ⊆ A' := by
  obtain ⟨Z, -, -, hA', hZopen, hcase⟩ := h
  rcases hcase with ⟨hcover, hdisj⟩ | ⟨hcover, -⟩
  · exact Obstruction.boxRegion_subset_of_surgeryStepZero htwo hA' hZopen hcover hdisj
      hupper hlower
  · rw [hcover]
    exact Set.subset_union_left

/-- **The piece removed by such a surgery misses the region inside the box entirely.** -/
theorem inter_removed_eq_empty {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (htwo : SliceLocallyTwoSided P s c σ u) {A' Z : Set R3}
    (hA' : Work.SurgeryInvariance.IsOpenInCarrier P A')
    (hZ : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hcover : Work.BoxShrink.Core.boxRegion P s c σ = A' ∪ Z) (hdisj : Disjoint A' Z)
    (hupper : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ A')
    (hlower : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ A') :
    Z ∩ Work.BoxShrink.Core.boxRegion P s c σ = ∅ := by
  have hsub := Obstruction.boxRegion_subset_of_surgeryStepZero htwo hA' hZ hcover hdisj
    hupper hlower
  ext x
  constructor
  · rintro ⟨hxZ, hxB⟩
    exact (Set.disjoint_left.mp hdisj (hsub hxB)) hxZ
  · exact fun h => absurd h (by simp)

/-- **A `2`-surgery removes a *clopen* piece**: if it removes anything from a preconnected region
of the surface, the removed piece is the whole region. -/
theorem eq_empty_of_mem_removed {A A' Z : Set R3} (hAc : A ⊆ P.carrier)
    (hA' : Work.SurgeryInvariance.IsOpenInCarrier P A')
    (hZ : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hcover : A = A' ∪ Z) (hdisj : Disjoint A' Z) (hpre : IsPreconnected A)
    {x : R3} (hxZ : x ∈ Z) (hxA : x ∈ A) :
    A' = ∅ := by
  rcases Obstruction.surgeryStepZero_eq_self_or_empty hAc hA' hZ hcover hdisj hpre with h | h
  · exact absurd ((Set.disjoint_left.mp (h ▸ hdisj)) hxA hxZ) not_false
  · exact h

/-- **No single `2`-surgery can remove a point of the slice from a connected region**: if the
region of the surface is preconnected and a step `A = A' ⊔ Z` puts a point of the slice inside the
removed piece, then the whole region is deleted.

Together with `boxRegion_subset_of_surgeryStepZero_allCases` (a `2`-surgery starting at the region
inside the box and ending at a region containing both half-regions cannot have moved anything) this
is the obstruction to building Pardon's family out of `2`-surgeries: the pinch removes a *neck*,
and a `2`-surgery can only remove a piece which is clopen in the region. -/
theorem eq_empty_of_slice_mem_removed {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {A A' Z : Set R3} (hAc : A ⊆ P.carrier)
    (hA' : Work.SurgeryInvariance.IsOpenInCarrier P A')
    (hZ : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hcover : A = A' ∪ Z) (hdisj : Disjoint A' Z) (hpre : IsPreconnected A)
    {x : R3} (hxs : x ∈ Work.BoxShrink.Core.sliceRegion P s c σ u) (hxA : x ∈ A) (hxZ : x ∈ Z) :
    A' = ∅ := by
  have _ := hxs
  exact eq_empty_of_mem_removed hAc hA' hZ hcover hdisj hpre hxZ hxA

end

end Work.BoxShrink.Bubble
