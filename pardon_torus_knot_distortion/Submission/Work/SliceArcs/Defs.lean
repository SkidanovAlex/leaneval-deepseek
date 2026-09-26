import Submission.Work.CountedPinch.All
import Submission.Work.PinchFamily.All
import Submission.Work.PinchLemma3.ClosedDiscA.isOpenInCarrier_connectedComponentIn

/-!
# `Work.SliceArcs` — the arcs route of Pardon's counted Lemma 3, reduced to one span datum

Entry point: **`import Submission.Work.SliceArcs.All`** (this module is the vocabulary of the
chapter).  Namespace `Work.SliceArcs`, directory `Submission/Work/SliceArcs/`.

## What this chapter is

`Work.BoxShrink.Pinch.CountingHalf` — Pardon's Lemma 3 with the counting of his proof — is the
second field of the ledger `Work.BoxShrink.ClassicalInputs`.  The immediately preceding chapter
`Work.CountedPinch` reduced it to two *position* data of the cutting plane:

* the **plane route** (the compact case): `Work.CountedPinch.CountedSlicePlane` — the plane is
  transverse along the slice and the flat disc is sliced by the surface — whence
  `CountedSliceGood` (transverse, tame, inessential slice) and Pardon's push-off;
* the **arcs route** (the non-compact, generic case): `Work.CountedPinch.CountedSliceArcs` (the
  closure of the slice is a finite disjoint union of embedded arcs of the surface) together with
  `CountedSliceCrossing` (transversality), the *counted* drop datum `CountedDrop`, and the sibling
  chapter's carried classical input `Work.BoxShrink.Pinch.BoxSliceNice`.

This chapter attacks the **arcs route** and removes from it every input but the arc structure and a
single statement form of the pinch.  The mathematical observation is that the arc structure already
gives everything the plane-oriented hypotheses were used for — the inessentiality of the slice
(`Work.CountedPinch.no_essential_of_sliceArcsBody`) and its honest tameness
(`Work.CountedPinch.tameClosedSlice_of_sliceArcsBody`) — and that the pinch argument itself does not
need to know anything about the plane: what it needs is the **collar decomposition of the box
region**, i.e. the existence of an open piece `Z` of the surface containing the slice, contained in
the box region, with open complement in the box region, whose winding span vanishes
(`Work.PinchFamily.SpanCollarBody`).  The collar decomposition is a decomposition of the box region
into two *disjoint open* pieces, so every loop of the box region lies in one of them
(`Work.SurgeryInvariance.Span.curve_subset_of_union`), and one obtains the **span containment**

  `W(boxRegion) ≤ W(halves)`,

which gives Pardon's conclusion `BubbleHalf` directly (`bubbleHalf_of_windingSpan_le_halves`) — with
**no dichotomy, no `Work.BoxShrink.Pinch.BoxSliceNice`, no sphere count, no `CountedDrop` and no
genuinely transverse plane**.

## The residuals of this chapter

All five are bodies over the counted shell `Work.CountedPinch.Counted` of the crux; the guard
`ArcCondition P s c σ u` (the arc structure of the slice, `∃ β, SliceArcsBody P β s c σ u`) is what
makes them weaker than the residuals recorded by the preceding chapters.

* **`ArcSpan` (the sharpest form which needs no auxiliary input)**: at every counted configuration
  carrying the arc structure, `W(box) ≤ W(halves)`.  It is implied by `ArcCollar` and hence by the
  previously recorded sharpest residuals `Work.PinchFamily.PinchCollarSpan` / `PinchNeckCollar`, and
  its route (`countingHalf_of_countedSliceArcs_arcSpan`) needs **no** auxiliary input at all.
* **`ArcCollar`**: at every counted configuration carrying the arc structure, some collar of the
  slice inside the box has vanishing winding span.  This is the statement with the natural geometric
  reading (Pardon's Step 2: the piece of the surface through which the pinching sphere passes), and
  it is the form in which the chapter's certificates and negative results are stated.
* **`ArcCollarComponent`**: the same with the *canonical* collar — the union of the components of the
  box region meeting the slice — as the explicit witness; equivalent to `ArcCollar`.
* **`ArcNeckCollar`**: Pardon's own description of the changed piece — the collar's loops are matched
  by loops of a clean sphere meeting the counted curve in fewer than `I(F,β)` points.  This is the
  spelling in which the counting is spent *at the neck*.
* **`ArcDrop` (the weakest datum, at the cost of Pardon's dichotomy)**: the counted drop datum
  `Work.CountedPinch.CountedDrop` with the transversality and tameness hypotheses replaced by the arc
  structure.  It is implied by `CountedSliceCrossing ∧ CountedDrop`
  (`arcDrop_of_drop_crossing`): the arcs route of the preceding chapter needs one input fewer.

## Negative results, and the scope of the residuals

The residuals are *counted* statements, and that is essential: **all** of the statement forms above
are **false at the body level** at explicit configurations carrying the arc structure.  The span form
— the weakest of them — fails at the standard `9/5` configuration (`not_arcSpanBody_s18`), the collar
forms fail there and at the standard `5/2` configuration (`not_spanCollarBody_s18`,
`not_arcCollarBody_cex`), and the drop form fails at the sibling chapter's `RefuteDrop` configuration
(`not_arcDropBody_dropCex`); the uncounted forms are false outright (`not_dropCase`,
`Work.BoxShrink.PinchOff.not_smoothHalfS`, …).  What the counting has to exclude is exactly those
configurations — `Work.PinchCounted.no_counted_of_sphereTrace_essential` and `no_counted_threeHalves`
are the shape of the exclusion — so no residual of this chapter may be weakened to a statement of
pure general position.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.SliceArcs

noncomputable section

/-! ## The vocabulary of the configuration

These are the parent chapters' objects (definitionally), re-exported so that a caller of this
chapter never has to reach past its interface. -/

/-- The surface of a parametrised torus, inside Pardon's box `PBox s c σ`. -/
abbrev box (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Set R3 :=
  Work.BoxShrink.Core.boxRegion P s c σ

/-- The two half-regions of the box, cut out by the plane `{y (σ 2) = c (σ 2) + u}`. -/
abbrev halves (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.PinchCounted.PinchSweep.halves P s c σ u

/-- The **slice**: the trace of the cutting plane inside the box. -/
abbrev slice (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sliceRegion P s c σ u

/-- The trace of the box sphere `∂PBox s c σ` on the surface. -/
abbrev sphereTrace (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  Work.BoxShrink.Core.sphereSet c σ s

/-- The upper half-region of the box. -/
abbrev upper (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.upperRegion P s c σ u

/-- The lower half-region of the box. -/
abbrev lower (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.lowerRegion P s c σ u

/-! ## The arc structure, as a condition on the configuration

`Work.CountedPinch.SliceArcsBody P β s c σ u` does not mention `β`; the `β`-free form below is the
form in which this chapter consumes it. -/

/-- **The arc structure of the slice.**  The closure of the slice is covered by finitely many
pairwise disjoint embedded arcs of the surface lying in that closure
(`Work.CountedPinch.SliceArcsBody`).  This is Pardon's genuine trace structure in the case in which
the trace leaves the open box: the arcs are closed at the ends, their endpoints lying on the box
sphere. -/
def ArcCondition (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∃ β : Work.CoreTopology.ClosedCurve P, Work.CountedPinch.SliceArcsBody P β s c σ u

/-- The arc structure of a configuration is a property of the configuration alone: `SliceArcsBody`
does not mention its curve argument, so the residual `Work.CountedPinch.CountedSliceArcs` gives it
at every counted configuration. -/
theorem arcCondition_of_sliceArcsBody'_eq {P : Work.CoreTopology.ParamTorus}
    (β β' : Work.CoreTopology.ClosedCurve P) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.CountedPinch.SliceArcsBody P β s c σ u ↔
      Work.CountedPinch.SliceArcsBody P β' s c σ u := Iff.rfl

/-- The arc structure from any single instance. -/
theorem arcCondition_of_sliceArcsBody {P : Work.CoreTopology.ParamTorus}
    {β : Work.CoreTopology.ClosedCurve P} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.CountedPinch.SliceArcsBody P β s c σ u) : ArcCondition P s c σ u :=
  ⟨β, h⟩

/-! ## The collar form of the pinch

The *body* of the collar residual: at a configuration whose slice satisfies the arc structure there
is a collar of the slice inside the box of vanishing winding span.  This is
`Work.PinchFamily.SpanCollarBody` guarded by the arc condition; it is the *only* input the arcs
route of this chapter needs. -/

/-- **The body of the collar residual.**  `Z` is a collar of the pinch
(`Work.PinchFamily.IsPinchCollar`: open in the surface, containing the slice, contained in the box
region, with open complement in the box region) whose winding span vanishes. -/
def ArcCollarBody (P : Work.CoreTopology.ParamTorus) (_β : Work.CoreTopology.ClosedCurve P)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ArcCondition P s c σ u → Work.PinchFamily.SpanCollarBody P _β s c σ u

/-- **The collar residual of the arcs route**: at every counted configuration of the crux whose
slice closure is a finite disjoint union of embedded arcs, the slice can be thickened to a collar
inside the box of vanishing winding span. -/
def ArcCollar : Prop := Work.CountedPinch.Counted ArcCollarBody

theorem arcCollar_def :
    ArcCollar = Work.CountedPinch.Counted ArcCollarBody := rfl

/-- **The canonical collar of the slice inside the box**: the union of the connected components of
the box region which meet the slice.  It is the smallest pinch collar of the configuration, and it
is the set a prover of `ArcCollar` should control (`Collar.lean`). -/
def collar (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  ⋃ x ∈ slice P s c σ u, connectedComponentIn (box P s c σ) x

/-- **The collar residual in the componentwise spelling**, which is the form a prover should aim
at: at every counted configuration carrying the arc structure, the union of the connected components
of the box region which meet the slice carries no essential loop.  It is equivalent to `ArcCollar`
(`collar_span_iff`) once the canonical collar of `Collar.lean` is available. -/
def ArcCollarComponentBody (P : Work.CoreTopology.ParamTorus)
    (_β : Work.CoreTopology.ClosedCurve P) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ArcCondition P s c σ u → Work.SurgeryInvariance.WindingSpan P (collar P s c σ u) = ⊥

/-- The componentwise collar residual. -/
def ArcCollarComponent : Prop := Work.CountedPinch.Counted ArcCollarComponentBody

/-! ## The drop form of the pinch

The *counted* drop datum `Work.CountedPinch.CountedDrop` of the preceding chapter asks, at a
transverse and closed-tame configuration whose box sphere and slice are inessential: if the two
half-regions are inessential then the box region is at most one-dimensional.  The arc structure
supplies both the tameness and the inessentiality of the slice, so the transversality and tameness
hypotheses can be dropped from the body; this chapter's `ArcDrop` is the resulting residual, and it
is implied by `CountedSliceCrossing ∧ CountedDrop` (`arcDrop_of_drop_crossing`). -/

/-- **The body of the drop residual of the arcs route**: at a configuration carrying the arc
structure whose box-sphere trace and slice carry no essential loop, two inessential half-regions
force the region inside the box to be at most one-dimensional. -/
def ArcDropBody (P : Work.CoreTopology.ParamTorus) (_β : Work.CoreTopology.ClosedCurve P)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ArcCondition P s c σ u →
  ¬ P.ContainsEssentialLoop (sphereTrace s c σ) →
  ¬ P.ContainsEssentialLoop (slice P s c σ u) →
  Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) = ⊥ →
  Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (box P s c σ)) ≤ 1

/-- **The body of the span form of the pinch at the configurations carrying the arc structure**:
the region inside the box realises no more winding vectors than the two half-regions.  It is the
conclusion of a collar of vanishing span (`windingSpan_box_le_halves_of_isPinchCollar`), and it
implies the drop form (`arcDropBody_of_arcSpanBody`). -/
def ArcSpanBody (P : Work.CoreTopology.ParamTorus) (_β : Work.CoreTopology.ClosedCurve P)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ArcCondition P s c σ u →
    Work.SurgeryInvariance.WindingSpan P (box P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u)

/-- **The span residual of the arcs route**: Pardon's pinch in its strongest conclusion, the span
containment `W(box) ≤ W(halves)`, demanded at the configurations carrying the arc structure.  It is
implied by the collar residual `ArcCollar` and by the recorded `CountedSpanPushOff` at every
configuration carrying the arc structure. -/
def ArcSpan : Prop := Work.CountedPinch.Counted ArcSpanBody

/-- **The body of the matched-collar form of the residual**, in Pardon's own description of the
changed piece of his pinch: the collar's loops are matched, with their winding vectors, by loops of a
clean sphere which meets the counted curve `β` in fewer than `I(F,β)` points
(`Work.PinchFamily.NeckCollarBody`).  This is the spelling in which the *counting is spent at the
neck*; `arcCollarBody_of_arcNeckCollarBody` recovers the collar form from it. -/
def ArcNeckCollarBody (P : Work.CoreTopology.ParamTorus) (β : Work.CoreTopology.ClosedCurve P)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ArcCondition P s c σ u → Work.PinchFamily.NeckCollarBody P β s c σ u

/-- **The matched-collar residual of the arcs route**: at every counted configuration carrying the
arc structure, the collar of the slice can be chosen so that its loops are matched by loops of a
clean sphere meeting the knot fewer than `I(F,β)` times — Pardon's pinch with the counting at the
neck. -/
def ArcNeckCollar : Prop := Work.CountedPinch.Counted ArcNeckCollarBody

/-- **The drop residual of the arcs route**: the counted drop datum
(`Work.CountedPinch.CountedDrop`) with the transversality and tameness hypotheses replaced by the
arc structure. -/
def ArcDrop : Prop := Work.CountedPinch.Counted ArcDropBody

theorem arcDrop_def : ArcDrop = Work.CountedPinch.Counted ArcDropBody := rfl

end

end Work.SliceArcs
