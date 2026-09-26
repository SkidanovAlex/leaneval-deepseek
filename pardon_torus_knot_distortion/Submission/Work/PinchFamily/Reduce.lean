import Submission.Work.PinchFamily.Family

/-!
# The residuals give `CountedPinch`, and hence Pardon's Lemma 3

This module assembles the chapters of this area into the reduction the deliverable asks for:

```
Work.PinchFamily.PinchTransport  ⟹  Work.PinchCounted.CountedPinch
                                 ⟹  Work.BoxShrink.Pinch.CountingHalf
                                 ⟹  Work.BoxShrink.CruxCore
                                 ⟹  Submission.BoxShrinkStatement
                                 ⟹  Submission.pardon_torus_knot_distortion
```

`PinchTransport` is the push-off in loop-transport form (`Defs.lean`); the family it produces is
constructed in `Family.lean`, and the implication `CountedPinch ⟹ CountingHalf` is the previous
chapter's (`Work.PinchCounted.countingHalf_of_countedPinch`), as are all the later steps.

The two other residuals of this area reduce through the collar family of `CollarFamily.lean`; the
theorems here are stated for the push-off, which is the least structured of the three.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchFamily

noncomputable section

/-! ## From the residuals to `CountedPinch` -/

/-- **The push-off residual gives the local residual of Pardon's counted Lemma 3.** -/
theorem countedPinch_of_pinchTransport (h : PinchTransport) :
    Work.PinchCounted.CountedPinch := by
  rw [countedPinch_eq_residual_localFamilyBody]
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact exists_region_of_regionPushOff (P := Work.Smooth.Morse.torus ψ) _ <|
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU

/-- **The push-off at one configuration gives the span containment of Pardon's Lemma 3.**  The two
half-regions are contained in the box region, and a transport preserves the winding span. -/
theorem windingSpan_halves_le_box_of_regionPushOff {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : RegionPushOff P s c σ u) :
    Work.SurgeryInvariance.WindingSpan P (halves P s c σ u) ≤
      Work.SurgeryInvariance.WindingSpan P (box P s c σ) :=
  (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq h).le

/-- **The push-off residual gives the span containment** — the statement-only form
`Work.PinchCounted.CountedSpanPushOff` of the previous chapter. -/
theorem countedSpanPushOff_of_pinchTransport (h : PinchTransport) :
    Work.PinchCounted.CountedSpanPushOff :=
  Work.PinchCounted.countedSpanPushOff_of_countedPinch (countedPinch_of_pinchTransport h)

/-! ## Through the ledger to Pardon's theorem -/

/-- **Pardon's Lemma 3 in the counted form, from the push-off residual.** -/
theorem countingHalf_of_pinchTransport (h : PinchTransport) :
    Work.BoxShrink.Pinch.CountingHalf :=
  Work.PinchCounted.countingHalf_of_countedPinch (countedPinch_of_pinchTransport h)

/-- **Pardon's shrinking step from the push-off residual.** -/
theorem cruxCore_of_pinchTransport (h : PinchTransport) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_pinchTransport h)

/-- **`Submission.BoxShrinkStatement` from the push-off residual** (with the two remaining
classical inputs: Pardon's cut-and-paste and the almost-everywhere general position). -/
theorem boxShrink_of_pinchTransport (h : PinchTransport)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux fun p q =>
    ⟨Work.BoxShrink.cleansDiscsAll_of_pushThrough hpush,
      cruxCore_of_pinchTransport h p q,
      Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis⟩

/-- **Pardon's theorem from the push-off residual and Pardon's cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_pinchTransport (h : PinchTransport)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_pinchTransport h)⟩

end

end Work.PinchFamily
