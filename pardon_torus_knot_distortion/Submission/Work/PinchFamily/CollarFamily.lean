import Submission.Work.PinchFamily.Reduce
import Submission.Work.PinchFamily.Collar
import Submission.Work.PinchFamily.collarRegion_localMoves
import Submission.Work.PinchFamily.spanCollarBody_of_neckCollarBody

/-!
# The collar residuals give `CountedPinch`

`Collar.lean` builds the two steps of the collar family of Pardon's pinch (the collar is removed;
the collar is pushed into the two half-regions), and the delegated lemma
`Work.PinchFamily.collarRegion_localMoves` gives the ε-form of its local moves.

This module assembles them: the collar family exists whenever there is a collar of vanishing
winding span, whence

```
Work.PinchFamily.PinchCollarSpan  ⟹  Work.PinchCounted.CountedPinch
Work.PinchFamily.PinchNeckCollar  ⟹  Work.PinchFamily.PinchCollarSpan
```

and — through the previous chapter's `countingHalf_of_countedPinch` — Pardon's Lemma 3, the crux and
the challenge, exactly as for the push-off residual of `Reduce.lean`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchFamily

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The collar family -/

/-- **A collar of vanishing winding span gives the family of `CountedPinch`.**  The three-piece
family of `Collar.lean` starts at the box region, ends at the two half-regions (with the empty extra
piece), and its two steps are `SurgeryStepZero`s with changed pieces `Z` and `halves ∩ Z`. -/
theorem exists_region_of_collar {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {Z : Set R3}
    (hZ : IsPinchCollar P s c σ u Z)
    (hspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (β : Work.CoreTopology.ClosedCurve P) : LocalFamilyBody P β s c σ u :=
  ⟨collarRegion P s c σ u Z, collarRegion_zero,
    ⟨∅, Work.BoxShrink.Pinch.isOpenInCarrier_empty P, Work.BoxShrink.Pinch.windingSpan_empty P,
      by simp, by rw [collarRegion_one, Set.union_empty]⟩,
    fun t => collarRegion_localMoves hZ hspan β t⟩

/-- **The span collar gives the family of Pardon's counted Lemma 3.** -/
theorem localFamilyBody_of_spanCollarBody (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : SpanCollarBody P β s c σ u) :
    LocalFamilyBody P β s c σ u := by
  obtain ⟨Z, hZ, hspan⟩ := h
  exact exists_region_of_collar hZ hspan β

/-- **The matched collar gives the family of Pardon's counted Lemma 3**: Pardon's counting lemma
(Pardon's Lemma 2, `Work.PinchCounted.CountedSweep.windingSpan_eq_bot_of_loops_match`) turns the
matching of the loops of the collar by loops of a clean low-count sphere into the vanishing of the
winding span of the collar. -/
theorem localFamilyBody_of_neckCollarBody (β : Work.CoreTopology.ClosedCurve P) {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : NeckCollarBody P β s c σ u) :
    LocalFamilyBody P β s c σ u :=
  localFamilyBody_of_spanCollarBody β (spanCollarBody_of_neckCollarBody β h)

/-! ## The residuals, lifted to the counted configurations -/

/-- **Residual 3 gives residual 2**: the matched collar has a vanishing winding span (Pardon's
Lemma 2 at the intermediate sphere). -/
theorem pinchCollarSpan_of_pinchNeckCollar (h : PinchNeckCollar) : PinchCollarSpan := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact spanCollarBody_of_neckCollarBody _ <|
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU

/-- **The collar residual gives the local residual of Pardon's counted Lemma 3.** -/
theorem countedPinch_of_pinchCollarSpan (h : PinchCollarSpan) :
    Work.PinchCounted.CountedPinch := by
  rw [countedPinch_eq_residual_localFamilyBody]
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact localFamilyBody_of_spanCollarBody _ <|
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU

/-- **The matched-collar residual gives the local residual of Pardon's counted Lemma 3.** -/
theorem countedPinch_of_pinchNeckCollar (h : PinchNeckCollar) :
    Work.PinchCounted.CountedPinch :=
  countedPinch_of_pinchCollarSpan (pinchCollarSpan_of_pinchNeckCollar h)

/-! ## Through the ledger to Pardon's theorem -/

/-- **Pardon's Lemma 3 in the counted form, from the collar residual.** -/
theorem countingHalf_of_pinchCollarSpan (h : PinchCollarSpan) :
    Work.BoxShrink.Pinch.CountingHalf :=
  Work.PinchCounted.countingHalf_of_countedPinch (countedPinch_of_pinchCollarSpan h)

/-- **Pardon's Lemma 3 in the counted form, from the matched-collar residual.** -/
theorem countingHalf_of_pinchNeckCollar (h : PinchNeckCollar) :
    Work.BoxShrink.Pinch.CountingHalf :=
  Work.PinchCounted.countingHalf_of_countedPinch (countedPinch_of_pinchNeckCollar h)

/-- **Pardon's shrinking step from the collar residual.** -/
theorem cruxCore_of_pinchCollarSpan (h : PinchCollarSpan) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_pinchCollarSpan h)

/-- **`Submission.BoxShrinkStatement` from the collar residual.** -/
theorem boxShrink_of_pinchCollarSpan (h : PinchCollarSpan)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux fun p q =>
    ⟨Work.BoxShrink.cleansDiscsAll_of_pushThrough hpush,
      cruxCore_of_pinchCollarSpan h p q,
      Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis⟩

/-- **Pardon's theorem from the collar residual and Pardon's cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_pinchCollarSpan (h : PinchCollarSpan)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_pinchCollarSpan h)⟩

/-- **Pardon's theorem from the matched-collar residual and Pardon's cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_pinchNeckCollar (h : PinchNeckCollar)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_pinchNeckCollar h)⟩

end

end Work.PinchFamily
