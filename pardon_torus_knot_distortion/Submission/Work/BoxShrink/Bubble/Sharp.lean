import Submission.Work.BoxShrink.Bubble.Equivalence
import Submission.Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty

/-!
# The sharp obstruction: a `2`-surgery never removes a slice point from a connected region

`Work.BoxShrink.Bubble.Obstruction` shows that a *single* `SurgeryStepZero` starting at the region
inside the box and ending at a region containing both half-regions must have changed nothing, under
the local-flatness hypothesis `SliceLocallyTwoSided`.  This file removes that hypothesis, and
sharpens the conclusion to the form in which chained surgeries are analysed:

**Heuristic.**  A `SurgeryStepZero P A A'` changes the region by an open piece `Z` of the surface
with vanishing winding span, the two pieces being open in the surface and disjoint.  In the removal
case `A = A' ∪ Z` the piece `Z` is *clopen in `A`*: `Z` is open and `A ∖ Z = A'` is open.
Consequently `Z ∩ boxRegion` is clopen in `boxRegion` (as long as `boxRegion ⊆ A`, so that
`boxRegion ∖ Z = boxRegion ∩ (A ∖ Z)`), and a *preconnected* `boxRegion` therefore lies either in
`Z` or in its complement.  If it lies in `Z` then
`WindingSpan P (boxRegion) ≤ WindingSpan P Z = ⊥`; so for a box region carrying an essential loop,
it is disjoint from `Z`.

**The theorem** (`sliceRegion_inter_eq_of_surgeryStepZero`): if `boxRegion` is preconnected and
carries an essential loop then a single `2`-surgery whose source contains `boxRegion` **does not
change the intersection with the slice**:

  `A' ∩ sliceRegion = A ∩ sliceRegion`.

Since the conclusion says in particular that the slice's points inside `A` survive, it applies
again to the next surgery of a chain (the next source still contains `boxRegion`), so by induction
on a finite chain: **no chain of `2`-surgeries removes the slice from a connected region that
carries an essential loop.**  The loop transport `Work.BoxShrink.Bubble.SlicePushOff` is therefore
unavoidable, and by `Work.BoxShrink.Bubble.bubbleSweep_nonempty_iff_slicePushOff` it *is* the
content of Pardon's double bubble in this configuration.

This is the formal counterpart of the observation recorded in `README.md`: Pardon's pinch has to
contain a genuine loop-level transport, and neither a single surgery nor any chain of them can
replace it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The trace on `boxRegion` of a set which is clopen in a region containing `boxRegion` is
clopen in `boxRegion`.** -/
theorem isOpenInCarrier_boxRegion_sdiff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {A Z : Set R3} (hbox : Work.BoxShrink.Core.boxRegion P s c σ ⊆ A)
    (hAZ : Work.SurgeryInvariance.IsOpenInCarrier P (A \ Z)) :
    Work.SurgeryInvariance.IsOpenInCarrier P (Work.BoxShrink.Core.boxRegion P s c σ \ Z) := by
  have hset : Work.BoxShrink.Core.boxRegion P s c σ \ Z =
      Work.BoxShrink.Core.boxRegion P s c σ ∩ (A \ Z) := by
    ext x
    constructor
    · rintro ⟨hx, hxZ⟩; exact ⟨hx, hbox hx, hxZ⟩
    · rintro ⟨hx, -, hxZ⟩; exact ⟨hx, hxZ⟩
  rw [hset, Work.SurgeryInvariance.IsOpenInCarrier, Set.preimage_inter]
  exact (Work.BoxShrink.Core.isOpenInCarrier_boxRegion P s c σ).inter hAZ

/-- **A piece which is clopen in a region containing `boxRegion` misses the box region**, when the
box region is preconnected and carries an essential loop. -/
theorem inter_eq_empty_of_clopen {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} (_u : ℝ)
    {A Z : Set R3} (hpre : IsPreconnected (Work.BoxShrink.Core.boxRegion P s c σ))
    (hspan : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥)
    (hbox : Work.BoxShrink.Core.boxRegion P s c σ ⊆ A) (_hAc : A ⊆ P.carrier)
    (hZopen : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hAZopen : Work.SurgeryInvariance.IsOpenInCarrier P (A \ Z))
    (hZspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥) :
    Z ∩ Work.BoxShrink.Core.boxRegion P s c σ = ∅ := by
  set B := Work.BoxShrink.Core.boxRegion P s c σ with hB
  -- open sets of `ℝ³` cutting out `Z` and `A ∖ Z` on the surface
  obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.mp (show IsOpen
    (Subtype.val ⁻¹' Z : Set P.carrier) from hZopen)
  obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp (show IsOpen
    (Subtype.val ⁻¹' (A \ Z) : Set P.carrier) from hAZopen)
  have hUc : P.carrier ∩ U = P.carrier ∩ Z :=
    Obstruction.carrier_inter_eq_of_preimage_eq hUeq
  have hVc : P.carrier ∩ V = P.carrier ∩ (A \ Z) :=
    Obstruction.carrier_inter_eq_of_preimage_eq hVeq
  have hBc : B ⊆ P.carrier := fun x hx => (Work.BoxShrink.Core.mem_boxRegion.mp hx).1
  -- the box region is covered by `U ∪ V`
  have hsub : B ⊆ U ∪ V := by
    intro x hx
    have hxA : x ∈ A := hbox hx
    by_cases hxZ : x ∈ P.carrier ∩ Z
    · left
      have : x ∈ P.carrier ∩ U := by rw [hUc]; exact hxZ
      exact this.2
    · right
      have hxni : x ∉ Z := fun hxZ' => hxZ ⟨hBc hx, hxZ'⟩
      have : x ∈ P.carrier ∩ V := by rw [hVc]; exact ⟨hBc hx, hbox hx, hxni⟩
      exact this.2
  have hBU : B ∩ U = B ∩ Z := by
    ext x
    constructor
    · rintro ⟨hx, hxU⟩
      have hc : x ∈ P.carrier := hBc hx
      have hx' : x ∈ P.carrier ∩ U := ⟨hc, hxU⟩
      rw [hUc] at hx'
      exact ⟨hx, hx'.2⟩
    · rintro ⟨hx, hxZ⟩
      refine ⟨hx, ?_⟩
      have hx' : x ∈ P.carrier ∩ Z := ⟨hBc hx, hxZ⟩
      rw [← hUc] at hx'
      exact hx'.2
  have hBV : B ∩ V = B ∩ (A \ Z) := by
    ext x
    constructor
    · rintro ⟨hx, hxV⟩
      have hc : x ∈ P.carrier := hBc hx
      have hx' : x ∈ P.carrier ∩ V := ⟨hc, hxV⟩
      rw [hVc] at hx'
      exact ⟨hx, hx'.2⟩
    · rintro ⟨hx, hxAZ⟩
      refine ⟨hx, ?_⟩
      have hx' : x ∈ P.carrier ∩ (A \ Z) := ⟨hBc hx, hxAZ⟩
      rw [← hVc] at hx'
      exact hx'.2
  have hempty : B ∩ (U ∩ V) = ∅ := by
    have h1 : B ∩ (U ∩ V) = (B ∩ U) ∩ (B ∩ V) := by
      ext x; simp only [Set.mem_inter_iff]; tauto
    rw [h1, hBU, hBV]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    exact (Set.disjoint_left.mp (Set.disjoint_sdiff_right (s := Z) (t := A)) hx.1.2) hx.2.2
  have hcases : B ∩ U = ∅ ∨ B ∩ V = ∅ := by
    by_contra h
    rw [not_or] at h
    exact (hpre U V hUopen hVopen hsub (Set.nonempty_iff_ne_empty.mpr h.1)
      (Set.nonempty_iff_ne_empty.mpr h.2)).ne_empty hempty
  rcases hcases with hU0 | hV0
  · rw [Set.inter_comm]
    rw [← hBU]
    exact hU0
  · exfalso
    have hsubZ : B ⊆ Z := by
      intro x hx
      by_contra hxZ
      have hxV : x ∈ B ∩ V := ⟨hx, by
        have h' : x ∈ P.carrier ∩ V := by
          rw [hVc]
          exact ⟨hBc hx, hbox hx, hxZ⟩
        exact h'.2⟩
      rw [hV0] at hxV
      exact hxV
    exact hspan (bot_unique (hZspan ▸ Work.SurgeryInvariance.WindingSpan_mono P hsubZ))

/-- **A single `2`-surgery does not remove a slice point from a region containing a preconnected
box region carrying an essential loop.** -/
theorem sliceRegion_inter_eq_of_surgeryStepZero {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {A A' : Set R3} (hpre : IsPreconnected (Work.BoxShrink.Core.boxRegion P s c σ))
    (hspan : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥)
    (hbox : Work.BoxShrink.Core.boxRegion P s c σ ⊆ A) (hAc : A ⊆ P.carrier)
    (h : Work.SurgeryInvariance.SurgeryStepZero P A A') :
    A' ∩ Work.BoxShrink.Core.sliceRegion P s c σ u =
      A ∩ Work.BoxShrink.Core.sliceRegion P s c σ u := by
  obtain ⟨Z, hZspan, hAopen, hA'open, hZopen, hcase⟩ := h
  have hsliceB : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆
      Work.BoxShrink.Core.boxRegion P s c σ := Work.BoxShrink.Core.sliceRegion_subset P s c σ u
  rcases hcase with ⟨hcover, hdisj⟩ | ⟨hcover, hdisj⟩
  · -- removal: `A = A' ∪ Z`, i.e. `A' = A \ Z` with `Z` clopen in `A`
    have hAZeq : A \ Z = A' := by
      ext x
      constructor
      · rintro ⟨hxA, hxZ⟩
        rcases (hcover ▸ hxA : x ∈ A' ∪ Z) with h | h
        · exact h
        · exact absurd h hxZ
      · intro hx
        exact ⟨hcover ▸ Or.inl hx, fun hxZ => (Set.disjoint_left.mp hdisj hx) hxZ⟩
    have hZempty : Z ∩ Work.BoxShrink.Core.boxRegion P s c σ = ∅ :=
      inter_eq_empty_of_clopen (P := P) (s := s) (c := c) (σ := σ) (_u := u) hpre hspan hbox hAc
        hZopen (hAZeq ▸ hA'open) hZspan
    have hsliceZ : Z ∩ Work.BoxShrink.Core.sliceRegion P s c σ u = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have h1 : x ∈ Z ∩ Work.BoxShrink.Core.boxRegion P s c σ := ⟨hx.1, hsliceB hx.2⟩
      exact (hZempty ▸ h1 : x ∈ (∅ : Set R3))
    rw [hcover, Set.union_inter_distrib_right, hsliceZ, Set.union_empty]
  · -- growth: `A' = A ∪ Z` with `Z` disjoint from `A`
    have hsliceZ : Z ∩ Work.BoxShrink.Core.sliceRegion P s c σ u = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      exact (Set.disjoint_left.mp hdisj (hbox (hsliceB hx.2))) hx.1
    rw [hcover, Set.union_inter_distrib_right, hsliceZ, Set.union_empty]

end

end Work.BoxShrink.Bubble
