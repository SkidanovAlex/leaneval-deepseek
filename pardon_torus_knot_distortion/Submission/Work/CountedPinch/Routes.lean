import Submission.Work.CountedPinch.Defs
import Submission.Work.CountedPinch.tameSlice_of_slicedPlane

/-!
# The two routes of the counted chapter

This module proves the reductions of the chapter, inside the counted vocabulary:

* `countedSliceGood_of_countedSlicePlane` — the general-position datum of the cutting plane
  (`TransverseSlice` + a planar slicing of the flat disc) gives the three hypotheses the transport
  theorem consumes (`TransverseSlice`, `TameSlice`, the inessentiality of the slice).  The third is
  **derived from the counting** (`sliceTrace_inessential_of_slicedPlane`, Pardon's Lemma 2 at the
  flat disc: the slicing datum supplies the innermost disc, the cut-and-paste `CleansDiscs` is a
  hypothesis of the counted configuration, and the plane count contradicts a compressing loop);
* `pinchTransport_of_countedSliceGood` — those three hypotheses give Pardon's push-off, through the
  workspace's capstone `Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice`;
* and the whole chain to the challenge, `countedPinch_of_countedSliceGood`,
  `countingHalf_of_countedSliceGood`, `cruxCore_of_countedSliceGood`,
  `boxShrink_of_countedSliceGood`, `pardon_torus_knot_distortion_of_countedSliceGood`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.CountedPinch

noncomputable section

/-! ## Pardon's Lemma 2 at the flat disc, from the counting -/

/-- **The slice carries no essential loop**, from the counting.

At the data of a counted configuration, if

* the flat disc `cutDisc s c σ u` is *sliced* by the surface
  (`Work.Smooth.Plane.SlicedPlane`: finitely many pairwise disjoint simple circles and embedded
  arcs, with the innermost-disc and covering properties of the planar general position), and
* the cut-and-paste `Work.InnermostDisk.CleansDiscs` holds at the surface, and
* the number of *parameters* at which the knot meets the cutting plane inside the box is at most
  `5(1+ε)/ε·d` with `countConst · d = 150 d < min p q = I(F,β)` (the counted configuration's plane
  count),

then the slice contains no essential loop of the surface: the sliding datum provides the innermost
disc (`Work.Smooth.Plane.innermostDiscInput_of_slicedPlane`), so a compressing loop inside the flat
disc meeting the knot in fewer than `I(F,β)` points contradicts the definition of `I(F,β)`. -/
theorem sliceTrace_inessential_of_slicedPlane
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hslice : Work.Smooth.Plane.SlicedPlane (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.cutDisc s c σ u))
    (hcl : Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) :=
  Work.PinchCounted.sliceTrace_inessential_of_counts p q hp hq hc ψ K hd himg hsmall hs c σ u
    (Work.InnermostDisk.cleansInSphere_of_inputs
      (Work.Smooth.Plane.innermostDiscInput_of_slicedPlane hslice) hcl) hcount

/-! ## The general position of the cutting plane gives the three hypotheses of the transport -/

/-- **The three hypotheses of the transport theorem, from the general position of the cutting
plane.**  At every counted configuration, `TransverseSlice` and a planar slicing of the flat disc
give `TransverseSlice`, `TameSlice` (the tameness, read off the slicing datum) and the
inessentiality of the slice (from the counting, `sliceTrace_inessential_of_slicedPlane`). -/
theorem countedSliceGood_of_countedSlicePlane (h : CountedSlicePlane) : CountedSliceGood :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨hT, hSlice⟩ :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ⟨hT, tameSlice_of_slicedPlane hSlice,
      sliceTrace_inessential_of_slicedPlane p q hp hq hc ψ K hd himg hsmall
        (lt_trans hr hrs) c σ u hSlice hcl hU⟩

/-! ## The un-shelled form of the reduction

The chain above is stated in the shell of the counted configurations, so that its residuals are
comparable with `Work.PinchCounted.CountedPinch` and `Work.PinchFamily.PinchTransport`.  The
reduction itself is *sharper*: on this route the hypotheses of the shell that concern the *box
sphere* — the swept box with an essential loop (`HasEssBox`), the general position of the sphere
(`SlicedSphere`) and the sphere count — are never consumed.  The theorem below records that: the
push-off holds at *every* configuration whose cutting plane is transverse and tame, whose flat disc
is innermost-complete, and whose plane count is below `I(F,β)`. -/

/-- **Pardon's push-off from the plane datum, without the box-sphere hypotheses.**  The only
counted hypothesis consumed is the plane count. -/
theorem regionPushOff_of_planeData (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    {ψ : Submission.Diffeo} {K : Knot} {d : ℝ} (hd : 0 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hcl : Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ))
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hTa : Work.BoxShrink.Pinch.TameSlice ψ s c σ u)
    (hIn : Work.InnermostDisk.InnermostDiscInput (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.cutDisc s c σ u))
    (hU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d))) :
    Work.PinchFamily.RegionPushOff (Work.Smooth.Morse.torus ψ) s c σ u :=
  Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice hT hTa
    (Work.PinchCounted.sliceTrace_inessential_of_counts p q hp hq hc ψ K hd himg hsmall hs c σ u
      (Work.InnermostDisk.cleansInSphere_of_inputs hIn hcl) hU)

/-! ## The push-off, and the chain to the challenge -/

/-- **Pardon's push-off at every counted configuration, from the three hypotheses of the
transport.**  This is the workspace's capstone
`Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice`, read in the counted vocabulary: at
a transverse and tame configuration whose slice carries no essential loop, the region inside the
box and the two half-regions realise the same winding vectors. -/
theorem pinchTransport_of_countedSliceGood (h : CountedSliceGood) : PinchTransport :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨hT, hTa, hZ⟩ :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice hT hTa hZ

/-- **Pardon's push-off at every counted configuration, from the general position of the cutting
plane.** -/
theorem pinchTransport_of_countedSlicePlane (h : CountedSlicePlane) : PinchTransport :=
  pinchTransport_of_countedSliceGood (countedSliceGood_of_countedSlicePlane h)

/-- **The local residual of the counted chapter, from the general position of the cutting
plane.** -/
theorem countedPinch_of_countedSliceGood (h : CountedSliceGood) : CountedPinch :=
  Work.PinchFamily.countedPinch_of_pinchTransport (pinchTransport_of_countedSliceGood h)

theorem countedPinch_of_countedSlicePlane (h : CountedSlicePlane) : CountedPinch :=
  countedPinch_of_countedSliceGood (countedSliceGood_of_countedSlicePlane h)

/-- **Pardon's Lemma 3 in the counted form, from the general position of the cutting plane.** -/
theorem countingHalf_of_countedSliceGood (h : CountedSliceGood) :
    Work.BoxShrink.Pinch.CountingHalf :=
  Work.PinchCounted.countingHalf_of_countedPinch (countedPinch_of_countedSliceGood h)

theorem countingHalf_of_countedSlicePlane (h : CountedSlicePlane) :
    Work.BoxShrink.Pinch.CountingHalf :=
  countingHalf_of_countedSliceGood (countedSliceGood_of_countedSlicePlane h)

/-- **The crux of the challenge from the general position of the cutting plane.** -/
theorem cruxCore_of_countedSliceGood (h : CountedSliceGood) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.PinchCounted.cruxCore_of_countedPinch (countedPinch_of_countedSliceGood h)

theorem cruxCore_of_countedSlicePlane (h : CountedSlicePlane) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_countedSliceGood (countedSliceGood_of_countedSlicePlane h)

/-- **Pardon's shrinking step from the general position of the cutting plane** (with the remaining
classical input: the cut-and-paste `Work.Topology.Classical.PushThroughInnermost`; the
almost-everywhere general position of the *box sphere* is a theorem of the workspace). -/
theorem boxShrink_of_countedSliceGood (h : CountedSliceGood)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.PinchCounted.boxShrink_of_countedPinch (countedPinch_of_countedSliceGood h) hpush

theorem boxShrink_of_countedSlicePlane (h : CountedSlicePlane)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  boxShrink_of_countedSliceGood (countedSliceGood_of_countedSlicePlane h) hpush

/-- **Pardon's theorem, from the general position of the cutting plane and the cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_countedSliceGood (h : CountedSliceGood)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.PinchCounted.pardon_torus_knot_distortion_of_countedPinch
    (countedPinch_of_countedSliceGood h) hpush

theorem pardon_torus_knot_distortion_of_countedSlicePlane (h : CountedSlicePlane)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_countedSliceGood
    (countedSliceGood_of_countedSlicePlane h) hpush

/-! ## The sharpest spelling: the plane datum

The residual `CountedPlaneInput` asks only for the general position of the plane, the tameness of
the slice, and Pardon's planar innermost-disc step at the flat disc.  The counting turns the last
into the inessentiality of the slice, exactly as above. -/

/-- **The three hypotheses of the transport theorem, from the plane datum.** -/
theorem countedSliceGood_of_countedPlaneInput (h : CountedPlaneInput) : CountedSliceGood :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨hT, hTa, hIn⟩ :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ⟨hT, hTa,
      Work.PinchCounted.sliceTrace_inessential_of_counts p q hp hq hc ψ K hd himg hsmall
        (lt_trans hr hrs) c σ u
        (Work.InnermostDisk.cleansInSphere_of_inputs hIn hcl) hU⟩

/-- **The plane datum from the slicing datum** (a planar slicing of the flat disc gives both the
tameness and the innermost disc). -/
theorem countedPlaneInput_of_countedSlicePlane (h : CountedSlicePlane) : CountedPlaneInput :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨hT, hSlice⟩ :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ⟨hT, tameSlice_of_slicedPlane hSlice,
      Work.Smooth.Plane.innermostDiscInput_of_slicedPlane hSlice⟩

/-- **The plane datum from its uniform spelling.** -/
theorem countedPlaneInput_of_countedPlaneInputUniform (h : CountedPlaneInputUniform) :
    CountedPlaneInput :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨hT, hTa, hUni⟩ :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ⟨hT, hTa,
      hUni _ (Work.BoxShrink.Pinch.isConvexPlanar_cutDisc s c σ u) hTa⟩

/-- **The three hypotheses of the transport theorem, from the uniform plane datum.** -/
theorem countedSliceGood_of_countedPlaneInputUniform (h : CountedPlaneInputUniform) :
    CountedSliceGood :=
  countedSliceGood_of_countedPlaneInput (countedPlaneInput_of_countedPlaneInputUniform h)

/-- **The push-off from the plane datum.** -/
theorem pinchTransport_of_countedPlaneInput (h : CountedPlaneInput) : PinchTransport :=
  pinchTransport_of_countedSliceGood (countedSliceGood_of_countedPlaneInput h)

theorem pinchTransport_of_countedPlaneInputUniform (h : CountedPlaneInputUniform) : PinchTransport :=
  pinchTransport_of_countedPlaneInput (countedPlaneInput_of_countedPlaneInputUniform h)

/-- **The local residual of the counted chapter, from the plane datum.** -/
theorem countedPinch_of_countedPlaneInput (h : CountedPlaneInput) : CountedPinch :=
  countedPinch_of_countedSliceGood (countedSliceGood_of_countedPlaneInput h)

theorem countedPinch_of_countedPlaneInputUniform (h : CountedPlaneInputUniform) : CountedPinch :=
  countedPinch_of_countedPlaneInput (countedPlaneInput_of_countedPlaneInputUniform h)

/-- **Pardon's Lemma 3 in the counted form, from the plane datum.** -/
theorem countingHalf_of_countedPlaneInput (h : CountedPlaneInput) :
    Work.BoxShrink.Pinch.CountingHalf :=
  countingHalf_of_countedSliceGood (countedSliceGood_of_countedPlaneInput h)

theorem countingHalf_of_countedPlaneInputUniform (h : CountedPlaneInputUniform) :
    Work.BoxShrink.Pinch.CountingHalf :=
  countingHalf_of_countedPlaneInput (countedPlaneInput_of_countedPlaneInputUniform h)

/-- **The crux of the challenge from the plane datum.** -/
theorem cruxCore_of_countedPlaneInput (h : CountedPlaneInput) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_countedSliceGood (countedSliceGood_of_countedPlaneInput h)

/-- **Pardon's theorem from the plane datum and the cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_countedPlaneInput (h : CountedPlaneInput)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_countedSliceGood (countedSliceGood_of_countedPlaneInput h) hpush

theorem pardon_torus_knot_distortion_of_countedPlaneInputUniform (h : CountedPlaneInputUniform)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_countedPlaneInput
    (countedPlaneInput_of_countedPlaneInputUniform h) hpush


/-! ## Where the residuals of this chapter sit in the ladder of the counted form

The residuals of this chapter imply the push-off, hence the weakest statement-forms of the previous
chapters: `Work.PinchCounted.CountedSpanPushOff` (the span containment `W(box) ≤ W(halves)`) and
`Work.PinchCounted.CountedDim` (Pardon's Lemma 1 invariant, the equality of the dimensions). -/

/-- **The span containment of the counted form, from the plane datum.** -/
theorem countedSpanPushOff_of_countedSliceGood (h : CountedSliceGood) :
    Work.PinchCounted.CountedSpanPushOff :=
  Work.PinchFamily.countedSpanPushOff_of_pinchTransport (pinchTransport_of_countedSliceGood h)

theorem countedSpanPushOff_of_countedSlicePlane (h : CountedSlicePlane) :
    Work.PinchCounted.CountedSpanPushOff :=
  countedSpanPushOff_of_countedSliceGood (countedSliceGood_of_countedSlicePlane h)

theorem countedSpanPushOff_of_countedPlaneInput (h : CountedPlaneInput) :
    Work.PinchCounted.CountedSpanPushOff :=
  countedSpanPushOff_of_countedSliceGood (countedSliceGood_of_countedPlaneInput h)

/-- **Pardon's Lemma 1 invariant (the dimension equality of the counted form), from the plane
datum.** -/
theorem countedDim_of_countedSliceGood (h : CountedSliceGood) : Work.PinchCounted.CountedDim :=
  Work.PinchCounted.countedDim_of_countedSpanPushOff (countedSpanPushOff_of_countedSliceGood h)

theorem countedDim_of_countedSlicePlane (h : CountedSlicePlane) : Work.PinchCounted.CountedDim :=
  countedDim_of_countedSliceGood (countedSliceGood_of_countedSlicePlane h)

/-! ## The compact case, and the honest cases

The workspace's tameness predicate `TameSlice` (hence the phase of the reduction that consumes it)
forces the slice to be **compact**: its arcs are parametrised over the compact interval and are
required to lie in the flat disc, so the slice is a finite union of compact sets
(`Work.BoxShrink.PinchOff.isCompact_sliceRegion_of_tameSlice`).  Geometrically this is the case in
which the trace of the cutting plane does *not* leave the box: the slice is then a finite disjoint
union of circles of the surface.  The general case — the trace leaving the box through the sphere
`∂PBox s c σ`, which is the generic configuration and the case of Pardon's finger move — is the
arcs route of `Arcs.lean`, where the arcs are closed at the ends
(`CountedSliceArcs`, `SliceArcsBody`) and the conclusion is reached without the tameness predicate
`TameSlice`. -/

/-- **The plane datum of this chapter is a compact-slice datum.**  Recorded so that a caller knows
which case of the reduction each residual covers: `CountedSlicePlane`, `CountedPlaneInput` and
`CountedPlaneInputUniform` all contain `TameSlice`, hence apply to the configurations whose slice is
compact. -/
theorem isCompact_slice_of_tameSlice {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    IsCompact (slice (Work.Smooth.Morse.torus ψ) s c σ u) :=
  Work.BoxShrink.PinchOff.isCompact_sliceRegion_of_tameSlice h

end

end Work.CountedPinch
