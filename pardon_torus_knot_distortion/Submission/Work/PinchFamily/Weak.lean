import Submission.Work.PinchFamily.CollarFamily
import Submission.Work.PinchFamily.Instances

/-!
# The residuals, cut down to the configurations that need them

The three residuals of `Defs.lean` demand their geometric input at **every** counted configuration.
That is more than necessary: at a configuration whose slice trace is empty the family of
`Work.PinchCounted.CountedPinch` exists outright (`Instances.lean`), because the two endpoint regions
coincide.  This module records the *strictly weaker* residuals which only bite where the cutting
plane actually meets the surface inside the box:

* `Work.PinchFamily.SpanCollarOrEmpty` — either the slice trace is empty, or there is a collar of
  vanishing winding span;
* `Work.PinchFamily.PushOffOrEmpty` — either the slice trace is empty, or the push-off holds.

Each of them implies `Work.PinchCounted.CountedPinch` (hence Pardon's Lemma 3 in the counted form),
and each is implied by the corresponding unconditional residual.  They are the smallest residuals of
this area: no geometric input is asked for at the configurations which the empty-slice case already
settles.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchFamily

noncomputable section

/-! ## The weakened residuals -/

/-- **The collar residual, demanded only where the slice trace is non-empty.** -/
def SpanCollarOrEmpty : Prop :=
  Residual fun P _β s c σ u => slice P s c σ u = ∅ ∨ SpanCollarBody P _β s c σ u

/-- **The push-off residual, demanded only where the slice trace is non-empty.** -/
def PushOffOrEmpty : Prop :=
  Residual fun P _β s c σ u => slice P s c σ u = ∅ ∨ RegionPushOff P s c σ u

/-- **The matched-collar residual, demanded only where the slice trace is non-empty.** -/
def NeckCollarOrEmpty : Prop :=
  Residual fun P _β s c σ u => slice P s c σ u = ∅ ∨ NeckCollarBody P _β s c σ u

/-! ## The unconditional residuals imply the weak ones -/

theorem spanCollarOrEmpty_of_pinchCollarSpan (h : PinchCollarSpan) : SpanCollarOrEmpty :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    Or.inr (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)

theorem pushOffOrEmpty_of_pinchTransport (h : PinchTransport) : PushOffOrEmpty :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    Or.inr (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)

theorem neckCollarOrEmpty_of_pinchNeckCollar (h : PinchNeckCollar) : NeckCollarOrEmpty :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    Or.inr (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)

/-! ## The weak residuals imply `CountedPinch` -/

/-- **The weak collar residual gives the local residual of Pardon's counted Lemma 3.** -/
theorem countedPinch_of_spanCollarOrEmpty (h : SpanCollarOrEmpty) :
    Work.PinchCounted.CountedPinch := by
  rw [countedPinch_eq_residual_localFamilyBody]
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  rcases h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    with hemp | hcol
  · exact localFamilyBody_of_sliceRegion_empty _ hemp
  · exact localFamilyBody_of_spanCollarBody _ hcol

/-- **The weak push-off residual gives the local residual of Pardon's counted Lemma 3.** -/
theorem countedPinch_of_pushOffOrEmpty (h : PushOffOrEmpty) :
    Work.PinchCounted.CountedPinch := by
  rw [countedPinch_eq_residual_localFamilyBody]
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  rcases h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    with hemp | hpo
  · exact localFamilyBody_of_sliceRegion_empty _ hemp
  · exact localFamilyBody_of_regionPushOff _ hpo

/-- **The weak matched-collar residual gives the local residual of Pardon's counted Lemma 3.** -/
theorem countedPinch_of_neckCollarOrEmpty (h : NeckCollarOrEmpty) :
    Work.PinchCounted.CountedPinch := by
  rw [countedPinch_eq_residual_localFamilyBody]
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  rcases h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    with hemp | hneck
  · exact localFamilyBody_of_sliceRegion_empty _ hemp
  · exact localFamilyBody_of_neckCollarBody _ hneck

/-! ## Through the ledger to Pardon's theorem -/

theorem countingHalf_of_spanCollarOrEmpty (h : SpanCollarOrEmpty) :
    Work.BoxShrink.Pinch.CountingHalf :=
  Work.PinchCounted.countingHalf_of_countedPinch (countedPinch_of_spanCollarOrEmpty h)

theorem countingHalf_of_pushOffOrEmpty (h : PushOffOrEmpty) :
    Work.BoxShrink.Pinch.CountingHalf :=
  Work.PinchCounted.countingHalf_of_countedPinch (countedPinch_of_pushOffOrEmpty h)

theorem cruxCore_of_spanCollarOrEmpty (h : SpanCollarOrEmpty) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_spanCollarOrEmpty h)

theorem cruxCore_of_pushOffOrEmpty (h : PushOffOrEmpty) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_pushOffOrEmpty h)

theorem boxShrink_of_spanCollarOrEmpty (h : SpanCollarOrEmpty)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux fun p q =>
    ⟨Work.BoxShrink.cleansDiscsAll_of_pushThrough hpush,
      cruxCore_of_spanCollarOrEmpty h p q,
      Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis⟩

theorem pardon_torus_knot_distortion_of_spanCollarOrEmpty (h : SpanCollarOrEmpty)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_spanCollarOrEmpty h)⟩

theorem pardon_torus_knot_distortion_of_pushOffOrEmpty (h : PushOffOrEmpty)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_pushOffOrEmpty h)⟩

end

end Work.PinchFamily
