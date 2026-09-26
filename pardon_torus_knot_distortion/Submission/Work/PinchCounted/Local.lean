import Submission.Work.PinchCounted.CountedStep
import Submission.Work.PinchCounted.Span

/-!
# The local residual of Pardon's counted Lemma 3

`Assemble.lean` states the residual of the counted form as `CountedStep2`: *at every configuration
carrying the counting data of the crux there is a `CountedSweep`, the pinching family with its
intermediate spheres, their cleanings and their counts.*

That datum is more than is ever used.  Along the pinching family the only thing consumed is, at each
parameter, the *local move* of the region (a transport, a change by a countable collar, or a change
by a piece of vanishing winding span).  This module isolates exactly that as the `Prop`
`Work.PinchCounted.CountedPinch`:

> at every counted configuration there is a family of regions `region : ℝ → Set R3` from the region
> inside the box to the two half-regions together with an open piece of vanishing span, whose local
> move at every parameter is a `CountedStep P β` (with `β` the knot of the configuration).

The two theorems of this module are the reduction

```
Work.PinchCounted.CountedPinch  ⟹  Work.BoxShrink.Pinch.CountingHalf
```

(`countingHalf_of_countedPinch`, through the span equality along the family and Pardon's Lemma 2 at
the changed pieces), the consequence `countedSpanPushOff_of_countedPinch` (the family gives the span
containment), and the two forgetful maps which show that `CountedPinch` is the weakest of the
*family-based* residuals, implied by both of the previous ones:

```
Work.PinchCounted.CountedStep2        ⟹  CountedPinch     (countedStep_of_countedSweep)
Work.PinchCounted.CountedPinchSweep   ⟹  CountedPinch     (countedStep_of_sweepLoops)
```

No auxiliary data of `CountedSweep` is required: no global set of exceptional parameters, no global
sphere family, no ε-uniformity in the hypothesis — only the local move at each parameter.  (The
*statements* `CountedSpanPushOff` and `CountedDim`, which assert only the conclusion and pack in no
structure, are weaker still as obligations; see `Dim.lean`.)
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The endgame: a family of regions with `CountedStep` local moves -/

/-- **The span equality along a family of regions whose local moves are `CountedStep`s.**  This is
the engine of the endgame: the span is constant along the family
(`Work.SurgeryInvariance.eq_of_locally_const` and `CountedStep.windingSpan_eq`), and at the final
region it is the span of the two halves by `Work.SurgeryInvariance.Span.union_eq_sup` (both pieces
open and disjoint) and the vanishing of the span of the extra piece. -/
theorem windingSpan_eq_of_countedLocalFamily {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (β : Work.CoreTopology.ClosedCurve P) (region : ℝ → Set R3)
    (hzero : region 0 = Work.BoxShrink.Core.boxRegion P s c σ)
    {Z : Set R3} (hZopen : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hZspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (hZdisj : Disjoint (PinchSweep.halves P s c σ u) Z)
    (hone : region 1 = PinchSweep.halves P s c σ u ∪ Z)
    (hloc : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - t| < ε →
      CountedStep P β (region t) (region r)) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) =
      Work.SurgeryInvariance.WindingSpan P (PinchSweep.halves P s c σ u) := by
  have hconst : ∀ t : ℝ, Work.SurgeryInvariance.WindingSpan P (region t) =
      Work.SurgeryInvariance.WindingSpan P (region 0) := fun t =>
    Work.SurgeryInvariance.eq_of_locally_const (f := fun r : ℝ =>
      Work.SurgeryInvariance.WindingSpan P (region r)) (by
        intro t
        obtain ⟨ε, hε, h⟩ := hloc t
        exact ⟨ε, hε, fun r hr => (CountedStep.windingSpan_eq (h r hr)).symm⟩) t 0
  have hsplit : Work.SurgeryInvariance.WindingSpan P (region 1) =
      Work.SurgeryInvariance.WindingSpan P (PinchSweep.halves P s c σ u) := by
    rw [hone, Work.SurgeryInvariance.Span.union_eq_sup
      (PinchSweep.isOpenInCarrier_halves P s c σ u) hZopen hZdisj, hZspan, sup_bot_eq]
  rw [← hzero, ← hconst 1, hsplit]

/-- **Pardon's Lemma 3 conclusion from a family of regions whose local moves are `CountedStep`s.**
If `region 0` is the region inside the box and `region 1` is the two half-regions together with an
open piece of vanishing winding span disjoint from them, and every local move of the family is a
`CountedStep` (with respect to the knot `β`), then the winding span of the box region equals that of
the two half-regions — hence an essential loop of the box region survives to one of the halves. -/
theorem bubbleHalf_of_countedLocalFamily {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (β : Work.CoreTopology.ClosedCurve P) (region : ℝ → Set R3)
    (hzero : region 0 = Work.BoxShrink.Core.boxRegion P s c σ)
    {Z : Set R3} (hZopen : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hZspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (hZdisj : Disjoint (PinchSweep.halves P s c σ u) Z)
    (hone : region 1 = PinchSweep.halves P s c σ u ∪ Z)
    (hloc : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - t| < ε →
      CountedStep P β (region t) (region r)) :
    Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  have hspan := windingSpan_eq_of_countedLocalFamily β region hzero hZopen hZspan hZdisj hone hloc
  have hne : Work.SurgeryInvariance.WindingSpan P (PinchSweep.halves P s c σ u) ≠ ⊥ := by
    rw [← hspan]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hbox
  have hnot : ¬ (Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥) := by
    intro hcon
    exact hne (by rw [PinchSweep.windingSpan_halves P s c σ u, hcon.1, hcon.2, sup_bot_eq])
  rcases not_and_or.mp hnot with h | h
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp h)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp h)

/-! ## The residual -/

/-- **The local residual of Pardon's counted Lemma 3.**

At every configuration carrying the counting data of the crux there is a family of regions
`region : ℝ → Set R3` of the surface such that

* `region 0` is the region inside the box `PBox s c σ`;
* `region 1` is the two half-regions cut out by the plane together with an open piece `Z` of
  vanishing winding span disjoint from them (the trace of the pinched neck; in Pardon's
  construction `Z` is empty);
* every local move of the family is a `CountedStep` with respect to the knot `β` of the
  configuration: a transport of the loop content, a change by an open piece whose loops are matched
  by loops of a clean low-count sphere, or a change by an open piece of vanishing winding span.

This is Pardon's Step 2 stripped to what is used: his pinching family of spheres, with the counting
of his proof entering only through the local moves.  It is *weaker* than both previous residuals of
the chapter (`CountedStep2`, `CountedPinchSweep`): see `countedPinch_of_countedStep2` and
`countedPinch_of_countedPinchSweep`. -/
def CountedPinch : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∃ region : ℝ → Set R3,
            region 0 = Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ ∧
            (∃ Z : Set R3,
              Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) Z ∧
              Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) Z = ⊥ ∧
              Disjoint (PinchSweep.halves (Work.Smooth.Morse.torus ψ) s c σ u) Z ∧
              region 1 = PinchSweep.halves (Work.Smooth.Morse.torus ψ) s c σ u ∪ Z) ∧
            ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - t| < ε →
              CountedStep (Work.Smooth.Morse.torus ψ)
                (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
                  (Work.CoreTopology.standardCurve p q)) (region t) (region r)

/-- **Pardon's Lemma 3 in the counted form, from the local residual.** -/
theorem countingHalf_of_countedPinch (h : CountedPinch) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨region, hzero, ⟨Z, hZopen, hZspan, hZdisj, hone⟩, hloc⟩ :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    bubbleHalf_of_countedLocalFamily (P := Work.Smooth.Morse.torus ψ)
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)) region hzero hZopen hZspan hZdisj hone hloc

/-! ## The residual and the rest of the ladder -/

/-- **The counted Step 2 of the chapter gives the local residual.**  A `CountedSweep`'s local moves
are `CountedStep`s (`countedStep_of_countedSweep`); the regions and the endpoint pieces are carried
over verbatim. -/
theorem countedPinch_of_countedStep2 (h : CountedStep2) : CountedPinch :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨D, hzero, Z, hZopen, hZspan, hZdisj, hone⟩ :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ⟨D.region, hzero, ⟨Z, hZopen, hZspan, hZdisj, hone⟩,
      fun t => countedStep_of_countedSweep D t⟩

/-- **The span-preserving pinching family gives the local residual.**  A `PinchSweep`'s regions form
a family whose local moves are `CountedStep`s through the zero-span local model
(`countedStep_of_sweepLoops`). -/
theorem countedPinch_of_countedPinchSweep (h : CountedPinchSweep) : CountedPinch :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨D⟩ := h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ⟨D.sweep.region, D.zero, ⟨D.Z, D.Z_open, D.Z_span, D.Z_disj, D.one⟩,
      fun t => countedStep_of_sweepLoops (β := Work.CoreTopology.ClosedCurve.mapHomeomorph
        ψ.toHomeomorph (Work.CoreTopology.standardCurve p q)) D.sweep t⟩

theorem countedSpanPushOff_of_countedPinch (h : CountedPinch) : CountedSpanPushOff :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨region, hzero, ⟨Z, hZopen, hZspan, hZdisj, hone⟩, hloc⟩ :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    le_of_eq (windingSpan_eq_of_countedLocalFamily (P := Work.Smooth.Morse.torus ψ)
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)) region hzero hZopen hZspan hZdisj hone hloc)

/-! ## Through the ledger to the challenge -/

/-- **Pardon's shrinking step from the local residual.** -/
theorem cruxCore_of_countedPinch (h : CountedPinch) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_countedPinch h)

/-- **`Submission.BoxShrinkStatement` from the local residual** (with the two remaining classical
inputs: Pardon's cut-and-paste and the almost-everywhere general position). -/
theorem boxShrink_of_countedPinch (h : CountedPinch)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux fun p q =>
    ⟨Work.BoxShrink.cleansDiscsAll_of_pushThrough hpush,
      cruxCore_of_countedPinch h p q,
      Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis⟩

/-- **Pardon's theorem from the local residual and Pardon's cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_countedPinch (h : CountedPinch)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_countedPinch h)⟩

end

end Work.PinchCounted
