import Submission.Work.SliceArcs.Collar

/-!
# The arcs route to Pardon's counted Lemma 3, with the collar as the only input

This module wires the collar form of the pinch (`ArcCollar`, `Defs.lean`) and its two weaker
statement forms (`ArcSpan`, `ArcDrop`) to Pardon's Lemma 3 in the counted form, to the crux, to the
shrinking step and to the challenge itself.  The routes are

```
        CountedSliceArcs        the arc structure of the slice (position datum of the trace)
                +
        ArcCollar               a collar of the slice of vanishing winding span
                ↓  bubbleHalf_of_arcCondition_of_spanCollarBody
        Work.BoxShrink.Pinch.CountingHalf       (Pardon's Lemma 3 in the counted form)
                ↓  Work.BoxShrink.cruxCore_of_countingHalf
        Work.BoxShrink.CruxCore  ─→  Work.BoxShrink.BoxShrinkStatement  ─→  the challenge
```

and, with Pardon's dichotomy at the box region in place,

```
        CountedSliceArcs + ArcDrop + Work.BoxShrink.Pinch.BoxSliceNice        (the drop form)
        CountedSliceArcs + ArcSpan + Work.BoxShrink.Pinch.BoxSliceNice        (the span form)
```

The comparison with the preceding chapter is recorded as well: its arcs route
(`Work.CountedPinch.countingHalf_of_countedSliceArcs_countedDrop`) needs, besides the arc structure,
the transversality datum `Work.CountedPinch.CountedSliceCrossing`, the counted drop datum
`Work.CountedPinch.CountedDrop` and the general position of the box sphere.  The implication
`arcDrop_of_drop_crossing` proves that this chapter's `ArcDrop` is *implied* by that pair of data,
so the drop form of this chapter is a strictly smaller input; the collar form needs *neither* of the
two, and not the general position of the box sphere either.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.SliceArcs

noncomputable section

/-! ## Pardon's Lemma 3 in the counted form from the collar -/

/-- **Pardon's counted Lemma 3 from the arc structure and a collar of vanishing span.**  At every
counted configuration the arc structure gives the arc condition, the collar datum gives a collar of
the slice of vanishing winding span, and the collar gives Pardon's conclusion directly
(`bubbleHalf_of_arcCondition_of_spanCollarBody`).  On this route the counting of the crux is *not*
used at all, and neither is the general position of the box sphere nor the transversality of the
cutting plane. -/
theorem countingHalf_of_countedSliceArcs_arcCollar
    (hA : Work.CountedPinch.CountedSliceArcs) (hC : ArcCollar) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU =>
    bubbleHalf_of_arcCondition_of_spanCollarBody
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q))
      (arcCondition_of_sliceArcsBody
        (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
          hcountS hcountU))
      (hC p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU
        (arcCondition_of_sliceArcsBody
          (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
            hcountS hcountU)))

/-! ## The comparison with the preceding chapter's data -/

/-- **The drop datum of this chapter from the preceding chapter's drop and crossing data.**  The arc
structure supplies the tameness of the slice, the crossing datum supplies the transversality, and the
counted drop datum concludes.  So `ArcDrop` is a datum *implied* by the input of the preceding
chapter's arcs route: the route of this chapter needs one input fewer. -/
theorem arcDrop_of_drop_crossing (hdrop : Work.CountedPinch.CountedDrop)
    (hcross : Work.CountedPinch.CountedSliceCrossing) : ArcDrop :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU =>
    fun hA hS' hZ' hhalves => by
      obtain ⟨β, hβ⟩ := hA
      exact hdrop p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU
        (hcross p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
          hcountS hcountU)
        (Work.CountedPinch.tameClosedSlice_of_sliceArcsBody hβ)
        hS' hZ' hhalves

/-- **The span residual of this chapter from the collar residual.** -/
theorem arcSpan_of_arcCollar (hC : ArcCollar) : ArcSpan :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU hA => by
    obtain ⟨Z, hZ, hspan⟩ :=
      hC p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU hA
    exact windingSpan_box_le_halves_of_isPinchCollar hZ hspan

/-- **The drop residual of this chapter from the collar residual.** -/
theorem arcDrop_of_arcCollar (hC : ArcCollar) : ArcDrop :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU hA => by
    intro _hS _hZ hhalves
    obtain ⟨Z, hZ', hspan⟩ :=
      hC p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU hA
    exact finrank_box_le_one_of_windingSpan_le_halves
      (windingSpan_box_le_halves_of_isPinchCollar hZ' hspan) hhalves

/-! ## Pardon's Lemma 3 from the span form and from the drop form -/

/-- **Pardon's counted Lemma 3 from the arc structure and the span form.**  The span containment
`W(box) ≤ W(halves)` gives Pardon's conclusion *directly* (`bubbleHalf_of_windingSpan_le_halves`):
if the region inside the box carries an essential loop, so does one of the two half-regions.  On this
route no auxiliary input at all is needed — no dichotomy at the box region, no general position of
the box sphere, no cut-and-paste and no counting. -/
theorem countingHalf_of_countedSliceArcs_arcSpan
    (hA : Work.CountedPinch.CountedSliceArcs) (hsp : ArcSpan) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU =>
    bubbleHalf_of_windingSpan_le_halves
      (hsp p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU
        (arcCondition_of_sliceArcsBody
          (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
            hcountS hcountU)))

/-- **Pardon's counted Lemma 3 from the arc structure and the drop form.**  The sphere trace is
inessential by Pardon's Lemma 2 and the sphere count of the counted configuration, the arc structure
gives the inessentiality of the slice, the drop datum gives the dimension bound, and Pardon's
dichotomy at the box region turns the bound into Pardon's conclusion. -/
theorem countingHalf_of_countedSliceArcs_arcDrop
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hA : Work.CountedPinch.CountedSliceArcs) (hdr : ArcDrop) :
    Work.BoxShrink.Pinch.CountingHalf := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
    hcountS hcountU hboxEss
  by_contra hno
  have hS : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.PinchCounted.sphereTrace_inessential_of_counts p q hp hq hc ψ K hd himg hsmall
      (lt_trans hr hrs) c σ hslice hcl hcountS
  have hZ : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) :=
    Work.CountedPinch.no_essential_of_sliceArcsBody
      (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU)
  have hbot : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) = ⊥ := by
    rw [Work.SurgeryInvariance.Span.union_eq_sup
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion _ s c σ u)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion _ s c σ u)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion _ s c σ u)]
    have hup : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u) :=
      fun h => hno (Or.inl h)
    have hlo : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) :=
      fun h => hno (Or.inr h)
    rw [(Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mpr hup,
      (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mpr hlo, sup_bot_eq]
  have hfin :=
    hdr p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU
      (arcCondition_of_sliceArcsBody
        (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
          hcountS hcountU))
      hS hZ hbot
  have hdich := Work.BoxShrink.PinchOff.pardonDichotomy_boxRegion
    (ψ := ψ) (s := s) (c := c) (σ := σ) (hnice ψ s c σ) hS
  have htop : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) = ⊤ := by
    rcases hdich with hb | ht
    · exact absurd hboxEss ((Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mp hb)
    · exact ht
  have hfin2 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan
      (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) = 2 := by
    rw [htop, finrank_top, Module.finrank_prod]
    simp
  rw [hfin2] at hfin
  omega

/-! ## The crux, the shrinking step and the challenge -/

/-- **Pardon's double-bubble core from the collar route.** -/
theorem cruxCore_of_countedSliceArcs_arcCollar
    (hA : Work.CountedPinch.CountedSliceArcs) (hC : ArcCollar) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_countedSliceArcs_arcCollar hA hC)

/-- **Pardon's shrinking step from the collar route** (with Pardon's cut-and-paste as the only
remaining classical input). -/
theorem boxShrink_of_countedSliceArcs_arcCollar
    (hA : Work.CountedPinch.CountedSliceArcs) (hC : ArcCollar)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_countingHalf hpush
    (countingHalf_of_countedSliceArcs_arcCollar hA hC)

/-- **Pardon's theorem from the collar route.** -/
theorem pardon_torus_knot_distortion_of_countedSliceArcs_arcCollar
    (hA : Work.CountedPinch.CountedSliceArcs) (hC : ArcCollar)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, countingHalf_of_countedSliceArcs_arcCollar hA hC⟩

/-- **The crux from the drop route.** -/
theorem cruxCore_of_countedSliceArcs_arcDrop
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hA : Work.CountedPinch.CountedSliceArcs) (hdr : ArcDrop) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_countedSliceArcs_arcDrop hnice hA hdr)

/-- **Pardon's theorem from the drop route.** -/
theorem pardon_torus_knot_distortion_of_countedSliceArcs_arcDrop
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hA : Work.CountedPinch.CountedSliceArcs) (hdr : ArcDrop)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, countingHalf_of_countedSliceArcs_arcDrop hnice hA hdr⟩

/-- **Pardon's theorem from the span form** (with no auxiliary input beyond the cut-and-paste). -/
theorem pardon_torus_knot_distortion_of_countedSliceArcs_arcSpan
    (hA : Work.CountedPinch.CountedSliceArcs) (hsp : ArcSpan)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, countingHalf_of_countedSliceArcs_arcSpan hA hsp⟩

/-! ## The complementarity of the two routes

The two routes of the counted chapter are *provably* disjoint on the configurations with a non-empty
slice: the arc structure forces the slice to be non-compact
(`Work.CountedPinch.not_sliceArcsBody_of_isCompact`), while the tameness predicate of the plane route
forces it to be compact (`Work.CountedPinch.isCompact_slice_of_tameSlice`).  Hence, at a transverse
and tame configuration, the arc structure can hold only if the slice is empty.

So the two routes cover complementary configurations, and the *whole* remaining content of Pardon's
counted Lemma 3 is the disjunction `EitherRoute` below: prove the plane datum of the counted chapter,
or the arc structure together with the collar datum of this chapter.  Each disjunct is implied by
nothing weaker in the workspace, each gives `CountingHalf`, and the disjunction is therefore the
weakest of the recorded targets. -/

/-- **The complementarity of the two routes.**  At a transverse and tame configuration, the slice
cannot carry the arc structure unless it is empty — the arc structure forces a non-compact slice,
the tameness a compact one. -/
theorem slice_eq_empty_of_sliceArcsBody_of_tame_of_transverse {ψ : Submission.Diffeo}
    {β : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hA : Work.CountedPinch.SliceArcsBody (Work.Smooth.Morse.torus ψ) β s c σ u)
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hTa : Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    Work.CountedPinch.slice (Work.Smooth.Morse.torus ψ) s c σ u = ∅ := by
  by_contra hne
  exact Work.CountedPinch.not_sliceArcsBody_of_isCompact hT
    (Work.CountedPinch.isCompact_slice_of_tameSlice hTa)
    (Set.nonempty_iff_ne_empty.mpr hne) hA

/-- **The two routes together**: Pardon's counted Lemma 3 follows from the plane datum of the
counted chapter, or from the arc structure of the slice together with the *span* form of the pinch
at the configurations carrying it.  This is the weakest of the recorded targets: the span form is
implied by the collar form (`arcSpan_of_arcCollar`), hence by
`Work.PinchFamily.PinchCollarSpan`/`PinchNeckCollar`, and its route needs no auxiliary input at all.
It is provably *weaker* than either route's input alone (`eitherRoute_of_countedSlicePlane`,
`eitherRoute_of_countedSliceArcs_arcSpan`), and it implies `CountingHalf`. -/
def EitherRoute : Prop :=
  Work.CountedPinch.CountedSlicePlane ∨ (Work.CountedPinch.CountedSliceArcs ∧ ArcSpan)

theorem eitherRoute_of_countedSlicePlane (h : Work.CountedPinch.CountedSlicePlane) : EitherRoute :=
  Or.inl h

theorem eitherRoute_of_countedSliceArcs_arcSpan (hA : Work.CountedPinch.CountedSliceArcs)
    (hsp : ArcSpan) : EitherRoute :=
  Or.inr ⟨hA, hsp⟩

theorem eitherRoute_of_countedSliceArcs_arcCollar (hA : Work.CountedPinch.CountedSliceArcs)
    (hC : ArcCollar) : EitherRoute :=
  Or.inr ⟨hA, arcSpan_of_arcCollar hC⟩


/-- **Pardon's counted Lemma 3 from either of the two routes.** -/
theorem countingHalf_of_eitherRoute (h : EitherRoute) :
    Work.BoxShrink.Pinch.CountingHalf :=
  h.elim Work.CountedPinch.countingHalf_of_countedSlicePlane
    (fun h' => countingHalf_of_countedSliceArcs_arcSpan h'.1 h'.2)

/-- **The crux from either of the two routes.** -/
theorem cruxCore_of_eitherRoute (h : EitherRoute) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_eitherRoute h)

/-- **Pardon's theorem from either of the two routes.** -/
theorem pardon_torus_knot_distortion_of_eitherRoute (h : EitherRoute)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, countingHalf_of_eitherRoute h⟩

/-! ## Discharging the ledger

The ledger `Work.BoxShrink.ClassicalInputs` has two fields: Pardon's cut-and-paste
(`Work.BoxShrink.CleansDiscsAll`) and the double-bubble datum
(`Work.BoxShrink.BubbleDatum = Pinch.CountingHalf ∨ Pinch.SmoothHalfS`, whose second disjunct is
refuted, so only its first is usable).  The theorems below record how the second field is discharged
by the residuals of this chapter. -/

/-- **The ledger's double-bubble datum from the collar route.** -/
theorem bubbleDatum_of_countedSliceArcs_arcCollar
    (hA : Work.CountedPinch.CountedSliceArcs) (hC : ArcCollar) : Work.BoxShrink.BubbleDatum :=
  Or.inl (countingHalf_of_countedSliceArcs_arcCollar hA hC)

/-- **The ledger's double-bubble datum from either of the two routes.** -/
theorem bubbleDatum_of_eitherRoute (h : EitherRoute) : Work.BoxShrink.BubbleDatum :=
  Or.inl (countingHalf_of_eitherRoute h)

/-- **The ledger's second field from either of the two routes.** -/
theorem classicalInputs_of_eitherRoute (h : EitherRoute) (hpush : Work.BoxShrink.CleansDiscsAll) :
    Work.BoxShrink.ClassicalInputs :=
  ⟨hpush, bubbleDatum_of_eitherRoute h⟩

/-- **The ledger's second field from the collar route**, with the cut-and-paste in its classical
form. -/
theorem classicalInputs_of_countedSliceArcs_arcCollar
    (hA : Work.CountedPinch.CountedSliceArcs) (hC : ArcCollar)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    Work.BoxShrink.ClassicalInputs :=
  ⟨hpush, bubbleDatum_of_countedSliceArcs_arcCollar hA hC⟩

/-! ## The pointwise disjunction: the sharpest recorded target

`EitherRoute` asks for one of the two routes *globally*.  The two routes are, however, complementary
case by case (`slice_eq_empty_of_sliceArcsBody_of_tame_of_transverse`: the arc structure can only
hold at a transverse tame configuration if the slice is empty), and a prover may well be able to
supply different data at different configurations — the plane datum at the configurations with a
compact slice, the arc structure and the span datum at the others.  The `Prop` below records exactly
that: at *each* counted configuration, either the arc structure together with the span containment,
or the general position of the cutting plane (transversality together with the planar slicing of the
flat disc, the datum of the preceding chapter's plane route).  It is implied by `EitherRoute`, and it
implies Pardon's counted Lemma 3, so it is the weakest target this chapter can offer.

It is what saves the arcs route from a formal obstruction: the arc structure *cannot* hold at a
non-empty compact transverse slice (`not_arcCondition_std_equator`), so a target demanding the arc
structure at *every* counted configuration could only be met if the plane route's configurations
were empty; `PointwiseRoute` lets the plane datum take those over. -/

/-- **The body of the pointwise disjunctive target**: at a configuration, either the arc structure
together with the span containment, or the general position of the cutting plane. -/
def PointwiseRouteBody (ψ : Submission.Diffeo)
    (_β : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)) (_K : Knot) (_d : ℝ)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  (ArcCondition (Work.Smooth.Morse.torus ψ) s c σ u ∧
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (box (Work.Smooth.Morse.torus ψ) s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (halves (Work.Smooth.Morse.torus ψ) s c σ u)) ∨
    (Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧
      Work.Smooth.Plane.SlicedPlane (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))

/-- **The pointwise disjunctive target**: at every counted configuration, the arc structure together
with the span containment, or the general position of the cutting plane. -/
def PointwiseRoute : Prop := Work.CountedPinch.CountedD PointwiseRouteBody

/-- **Pardon's counted Lemma 3 from the pointwise disjunction.**  In the first case the span
containment gives Pardon's conclusion directly; in the second the plane datum gives, at that
configuration, the tameness of the slice and — from the plane count and the cut-and-paste of the
counted configuration — its inessentiality, whence the workspace's capstone
`Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice` gives the push-off, hence the span
equality, hence Pardon's conclusion. -/
theorem countingHalf_of_pointwiseRoute (h : PointwiseRoute) :
    Work.BoxShrink.Pinch.CountingHalf := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
    hcountS hcountU
  rcases h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU with ⟨_hA, hle⟩ | ⟨hT, hSP⟩
  · exact bubbleHalf_of_windingSpan_le_halves hle
  · have hTa : Work.BoxShrink.Pinch.TameSlice ψ s c σ u :=
      Work.CountedPinch.tameSlice_of_slicedPlane hSP
    have hZ : ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) :=
      Work.CountedPinch.sliceTrace_inessential_of_slicedPlane p q hp hq hc ψ K hd himg hsmall
        (lt_trans hr hrs) c σ u hSP hcl hcountU
    have hPO := Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice hT hTa hZ
    exact bubbleHalf_of_windingSpan_le_halves
      (le_of_eq (Work.PinchFamily.windingSpan_box_eq_halves_of_regionPushOff hPO))

/-- **`EitherRoute` implies the pointwise disjunction** (each of its disjuncts supplies the pointwise
disjunction at every configuration).  So the pointwise form is the weaker target. -/
theorem pointwiseRoute_of_eitherRoute (h : EitherRoute) : PointwiseRoute := by
  rcases h with hpl | ⟨hA, hsp⟩
  · -- the plane route: at each configuration the plane datum holds, giving the second disjunct
    exact fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU =>
      Or.inr (hpl p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU)
  · -- the arc route: at each configuration the arc structure and the span datum hold
    exact fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU =>
      Or.inl ⟨arcCondition_of_sliceArcsBody
          (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
            hcountS hcountU),
        hsp p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
          hcountS hcountU
          (arcCondition_of_sliceArcsBody
            (hA p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
              hcountS hcountU))⟩

/-- **The crux from the pointwise disjunction.** -/
theorem cruxCore_of_pointwiseRoute (h : PointwiseRoute) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_pointwiseRoute h)

/-- **Pardon's theorem from the pointwise disjunction.** -/
theorem pardon_torus_knot_distortion_of_pointwiseRoute (h : PointwiseRoute)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_pointwiseRoute h)⟩

/-- **The ledger's double-bubble datum from the pointwise disjunction.** -/
theorem bubbleDatum_of_pointwiseRoute (h : PointwiseRoute) : Work.BoxShrink.BubbleDatum :=
  Or.inl (countingHalf_of_pointwiseRoute h)

/-! ## Where the new residuals sit in the ladder of the development

The collar residual of this chapter is *weaker* than the sharpest residual recorded by the preceding
chapters, `Work.PinchFamily.PinchCollarSpan` — the same statement without the arc hypothesis: the
implication below is the formal statement of "the residual of this chapter is only demanded at the
configurations carrying the arc structure". -/

/-- **The collar residual of this chapter from the recorded sharpest collar residual.** -/
theorem arcCollar_of_pinchCollarSpan (h : Work.PinchFamily.PinchCollarSpan) : ArcCollar :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU =>
    fun _hA =>
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU

/-- **The collar residual of this chapter from the matched-collar residual**: Pardon's description
of the changed piece, with the counting spent at the neck, gives the vanishing of its span. -/
theorem arcCollar_of_arcNeckCollar (h : ArcNeckCollar) : ArcCollar :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU hA =>
    (arcCollarBody_of_arcNeckCollarBody
      (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
        hcountS hcountU)) hA

/-- **The matched-collar residual of this chapter from the recorded one** (without the arc
hypothesis). -/
theorem arcNeckCollar_of_pinchNeckCollar (h : Work.PinchFamily.PinchNeckCollar) : ArcNeckCollar :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU hA =>
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu
      hcountS hcountU

/-- **Pardon's counted Lemma 3 from the arc structure and the matched collar.** -/
theorem countingHalf_of_countedSliceArcs_arcNeckCollar
    (hA : Work.CountedPinch.CountedSliceArcs) (hN : ArcNeckCollar) :
    Work.BoxShrink.Pinch.CountingHalf :=
  countingHalf_of_countedSliceArcs_arcCollar hA (arcCollar_of_arcNeckCollar hN)

/-- **The drop residual of this chapter from the recorded sharpest collar residual.** -/
theorem arcDrop_of_pinchCollarSpan (h : Work.PinchFamily.PinchCollarSpan) : ArcDrop :=
  arcDrop_of_arcCollar (arcCollar_of_pinchCollarSpan h)

/-- **The span residual of this chapter from the recorded sharpest collar residual.** -/
theorem arcSpan_of_pinchCollarSpan (h : Work.PinchFamily.PinchCollarSpan) : ArcSpan :=
  arcSpan_of_arcCollar (arcCollar_of_pinchCollarSpan h)

end

end Work.SliceArcs
