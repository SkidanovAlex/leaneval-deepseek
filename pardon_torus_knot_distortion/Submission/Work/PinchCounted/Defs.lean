import Submission.Work.SurgeryInvariance.Loops
import Submission.Work.BoxShrink.Pinch.Defs
import Submission.Work.BoxShrink.ledger

/-!
# `Work.PinchCounted` — Pardon's double bubble in the counted form

Entry point: `import Submission.Work.PinchCounted.All`.
Namespace: `Work.PinchCounted`.  Directory: `Submission/Work/PinchCounted/`.

## What this chapter is

The challenge reduces (through `Work.BoxShrink.CruxCore`) to the single input
`Work.BoxShrink.Pinch.CountingHalf`, Pardon's Lemma 3 (`doublebubble`) at the configurations the
crux produces: those carrying a knot `β`, a distortion bound `d`, and the two intersection counts
`|S ∩ β| ≤ 75 d`, `|D ∩ β| ≤ 37.5 d` with `150 d < min p q = I(F,β)`.

This chapter

* isolates the **counted residual** in its exact geometric form (`CountedPinchSweep`, below):
  Pardon's pinching family of spheres, recorded through the regions it cuts out of the surface,
  with **span-preserving** local models — which is what his counting argument supplies;
* proves that this residual gives Pardon's Lemma 3 conclusion and hence the whole challenge
  (`PinchSweep.windingSpan_boxRegion_eq`, `bubbleHalf_of_pinchSweep` here;
  `countingHalf_of_countedPinchSweep`, `Main.lean`);
* proves the counting bridge: the crux's two counts give the two inessentiality facts of Pardon's
  Lemma 2 at the endpoints (`Counting.lean`);
* records that the *uncounted* route to the same conclusion needs an extra planar input, which the
  counted form does not (`Main.lean`, §"The uncounted route");
* gives non-vacuity instances of the residual (`Instances.lean`).

## Why the counted form, and why span-preserving local models

Pardon's proof of Lemma 3 does not use the inessentiality hypotheses at the two endpoints; it uses
his counting hypothesis `|S_t ∩ β| ≤ |S ∩ β| + 2|D ∩ β| < I(F,β)` at **every intermediate sphere**
`S_t` of the pinching family.  By Lemma `mustbeinessential` every curve of `S_t ∩ F` is therefore
inessential in `F`.  In the present vocabulary that means:

* every **changed piece** of the pinching family (the trace in `F` of the neck of the pinching
  sphere, i.e. a push-off of the slice) has vanishing winding span — the local model is
  `Work.SurgeryInvariance.SurgeryStepZero`, *not* the weaker `Work.BoxShrink.Bubble.SurgeryStepSmall`
  of Pardon's dichotomy argument;
* hence the winding span is **constant** along the whole family
  (`Work.SurgeryInvariance.SweepLoops.windingSpan_eq`), and no dichotomy, dimension count, or
  endgame step is needed at all.

This is why the counted form is strictly more than `Work.BoxShrink.Pinch.SmoothHalfS`: the local
models of the *counted* family are the zero-span ones.  `PinchSweep` is that family.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Pardon's pinch with span-preserving local models -/

/-- **Pardon's pinching family of spheres, recorded through the regions it cuts out of the
surface, with span-preserving local models.**

The family `sweep : Work.SurgeryInvariance.SweepLoops P` of regions `F ∩ int(S_t)`:

* `zero` — at time `0` the region is the region inside Pardon's box `PBox s c σ`;
* `one` — at time `1` the region is the two half-regions of the box cut by the plane
  `{y (σ 2) = c (σ 2) + u}`, together with a piece `Z` (the trace of the pinching disc, the
  perturbed double bubble of Pardon's `doublebubble2`);
* `Z_open`, `Z_span`, `Z_disj` — that piece is open in the surface, of vanishing winding span, and
  disjoint from the two half-regions.

The local models of `sweep` are *span-preserving* (`RegionEquivalent` away from the exceptional
parameters, `SurgeryStepZero` at them): this is exactly what Pardon's counting hypothesis supplies,
because every intermediate sphere meets the knot in fewer than `I(F,β)` points, so every changed
piece is inessential.

Consequently the winding span is constant along the family — no dichotomy, no dimension count and
no endgame hypothesis is needed to pass the pinching parameter. -/
structure PinchSweep (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) where
  /-- the family of regions `F ∩ int(S_t)`, with span-preserving local models -/
  sweep : Work.SurgeryInvariance.SweepLoops P
  /-- at time `0` the region is the region inside the box -/
  zero : sweep.region 0 = Work.BoxShrink.Core.boxRegion P s c σ
  /-- the piece of the surface through which the pinch passes -/
  Z : Set R3
  /-- it is open in the surface -/
  Z_open : Work.SurgeryInvariance.IsOpenInCarrier P Z
  /-- it contributes nothing to the winding span -/
  Z_span : Work.SurgeryInvariance.WindingSpan P Z = ⊥
  /-- it is disjoint from the two half-regions -/
  Z_disj : Disjoint (Work.BoxShrink.Core.upperRegion P s c σ u ∪
    Work.BoxShrink.Core.lowerRegion P s c σ u) Z
  /-- at time `1` the region is the two half-regions together with that piece -/
  one : sweep.region 1 =
    (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) ∪ Z

namespace PinchSweep

/-- The two half-regions of the box, as a set. -/
abbrev halves (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u

variable {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- The two half-regions are open in the surface. -/
theorem isOpenInCarrier_halves (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.SurgeryInvariance.IsOpenInCarrier P (halves P s c σ u) :=
  Work.SurgeryInvariance.isOpenInCarrier_union (P := P)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)

/-- The winding span of the two half-regions is the supremum of the two halves' spans. -/
theorem windingSpan_halves (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) =
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
        Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) :=
  Work.SurgeryInvariance.Span.union_eq_sup
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)

/-- **The winding span of the box region is the winding span of the two half-regions.**  This is
Pardon's Lemma 3 in its span form, from the pinching family: the span is constant along the family
(`Work.SurgeryInvariance.SweepLoops.windingSpan_eq`), and at time `1` the family is the two
half-regions together with a piece of vanishing span, which contributes nothing
(`Work.SurgeryInvariance.Span.union_eq_sup`). -/
theorem windingSpan_boxRegion_eq (D : PinchSweep P s c σ u) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) =
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) := by
  have hconst : Work.SurgeryInvariance.WindingSpan P (D.sweep.region 1) =
      Work.SurgeryInvariance.WindingSpan P (D.sweep.region 0) :=
    Work.SurgeryInvariance.SweepLoops.windingSpan_eq D.sweep 1
  have hsplit : Work.SurgeryInvariance.WindingSpan P (D.sweep.region 1) =
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) := by
    rw [D.one]
    rw [Work.SurgeryInvariance.Span.union_eq_sup (isOpenInCarrier_halves P s c σ u) D.Z_open
      D.Z_disj, D.Z_span, sup_bot_eq]
  rw [← D.zero, ← hconst, hsplit]

/-- **A region which is the union of the two half-regions and an open piece of vanishing winding
span disjoint from them contains an essential loop iff one of the two half-regions does.** -/
theorem containsEssentialLoop_halves_of_union (D : PinchSweep P s c σ u)
    (h : P.ContainsEssentialLoop ((halves P s c σ u) ∪ D.Z)) :
    P.ContainsEssentialLoop (Work.BoxShrink.Core.upperRegion P s c σ u) ∨
      P.ContainsEssentialLoop (Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  have hsup : Work.SurgeryInvariance.WindingSpan P ((halves P s c σ u) ∪ D.Z) =
      Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) := by
    rw [Work.SurgeryInvariance.Span.union_eq_sup (isOpenInCarrier_halves P s c σ u) D.Z_open
      D.Z_disj, D.Z_span, sup_bot_eq]
  have hne : Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) ≠ ⊥ := by
    rw [← hsup]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr h
  have hnot : ¬ (Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥) := by
    intro hcon
    exact hne (by rw [windingSpan_halves P s c σ u, hcon.1, hcon.2, sup_bot_eq])
  rcases not_and_or.mp hnot with h | h
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp h)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp h)

end PinchSweep

/-- **Pardon's Lemma 3, `doublebubble`, from the pinch with span-preserving models.**  If the
region inside the box carries an essential loop, then so does one of the two half-regions: the
winding span is constant along the pinching family and the final region is the two half-regions
together with a piece of vanishing span. -/
theorem bubbleHalf_of_pinchSweep {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : PinchSweep P s c σ u) : Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  have h0 : P.ContainsEssentialLoop (D.sweep.region 0) := by rw [D.zero]; exact hbox
  have h1 : P.ContainsEssentialLoop (D.sweep.region 1) :=
    (D.sweep.containsEssentialLoop_iff 1).mpr h0
  rw [D.one] at h1
  exact D.containsEssentialLoop_halves_of_union h1

/-- **Pardon's Lemma 3 conclusion from the pinch, in the span form**: the winding span of the box
region is the winding span of the union of the two half-regions. -/
theorem windingSpan_boxRegion_eq_halves {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : PinchSweep P s c σ u) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) =
      Work.SurgeryInvariance.WindingSpan P
        (PinchSweep.halves P s c σ u) :=
  D.windingSpan_boxRegion_eq

end

end Work.PinchCounted
