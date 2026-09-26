import Submission.Work.PinchFamily.Weak
import Submission.Work.PinchFamily.regionPushOff_of_localFamilyBody

/-!
# The push-off residual is *necessary*, not only sufficient

`Reduce.lean` proves that the push-off residual `Work.PinchFamily.PinchTransport` implies the local
residual `Work.PinchCounted.CountedPinch`.  This module proves the converse, in the only case in
which it can hold:

> if the two half-regions carry an essential loop, then the family of `CountedPinch` **forces** the
> push-off.

The reason is that a `CountedStep` transports loops: each of its three local models, in the
direction in which a loop of one region is matched by a loop of the other, is a `RegionEquivalent`
once the target region is known to meet the carrier (case 2 uses Pardon's Lemma 2 at the
intermediate sphere, case 3 the vanishing of the span of the changed piece).  Along the family this
propagates by connectedness of `ℝ`, so the two endpoints are `RegionEquivalent` — and pushing the
trace of the slicing plane off into the two half-regions is precisely the push-off.

Consequently, *modulo the degenerate case in which the two half-regions carry no essential loop*
— in which Pardon's conclusion is empty — the local residual of Pardon's counted Lemma 3 **is** the
push-off of the slice, and nothing more: the family, its exceptional parameters and its local models
add nothing to the single geometric statement.

The degenerate case is handled by `Work.PinchFamily.PinchTransportEssential`, which demands the
push-off only where the two half-regions carry an essential loop; the chapter also proves that the
push-off holds at *every* counted configuration whose slice trace is empty
(`Instances.lean`), so the two spellings agree there as well.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchFamily

noncomputable section

/-- **The push-off residual, in the form in which it is necessary**: the push-off is demanded only
at counted configurations at which the two half-regions carry an essential loop, i.e. exactly where
Pardon's Lemma 3 has content. -/
def PinchTransportEssential : Prop :=
  Residual fun P _β s c σ u =>
    ¬ P.ContainsEssentialLoop (halves P s c σ u) ∨ RegionPushOff P s c σ u

/-- **Every counted configuration has an essential loop in the two half-regions**: the conclusion of
Pardon's Lemma 3 in the case in which the region inside the box carries one. -/
def HalvesEssentialAlways : Prop :=
  Residual fun P _β s c σ u => P.ContainsEssentialLoop (halves P s c σ u)

/-- **The push-off is a consequence of the local residual**, wherever the two half-regions carry an
essential loop. -/
theorem pinchTransportEssential_of_countedPinch (h : Work.PinchCounted.CountedPinch) :
    PinchTransportEssential := by
  rw [countedPinch_eq_residual_localFamilyBody] at h
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  by_cases hess : (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (halves (Work.Smooth.Morse.torus ψ) s c σ u)
  · exact Or.inr (regionPushOff_of_localFamilyBody _
      (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU) hess)
  · exact Or.inl hess

/-- **The push-off residual (with the degenerate case excluded) is equivalent to the local residual
of Pardon's counted Lemma 3.** -/
theorem countedPinch_of_pinchTransportEssential (h : PinchTransportEssential)
    (hess : HalvesEssentialAlways) : Work.PinchCounted.CountedPinch := by
  rw [countedPinch_eq_residual_localFamilyBody]
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  have hess' := hess p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice
    u hu hS hU
  rcases h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    with hneg | hpo
  · exact absurd hess' hneg
  · exact localFamilyBody_of_regionPushOff _ hpo

/-- The push-off residual gives the essential-halves form. -/
theorem pinchTransportEssential_of_pinchTransport (h : PinchTransport) :
    PinchTransportEssential :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    Or.inr (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice
      u hu hS hU)

/-- **Under the hypothesis that every counted configuration has an essential loop in the two
half-regions, the local residual of Pardon's counted Lemma 3 *is* the push-off.**  (That hypothesis
is exactly what `Work.BoxShrink.Pinch.CountingHalf` asserts at the configurations at which the
region inside the box carries an essential loop.) -/
theorem countedPinch_iff_pinchTransport_of_halvesEssential (h : HalvesEssentialAlways) :
    Work.PinchCounted.CountedPinch ↔ PinchTransport := by
  refine ⟨fun hc => ?_, countedPinch_of_pinchTransport⟩
  intro p q hp hq hc' ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  rcases pinchTransportEssential_of_countedPinch hc p q hp hq hc' ψ K d hd hbound himg hsmall hcl
      r hr c σ hbox s hrs hs hslice u hu hS hU with hneg | hpo
  · exact absurd (h p q hp hq hc' ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice
      u hu hS hU) hneg
  · exact hpo

/-! ## The residuals of the previous chapter imply the sharp form

Since `CountedPinch` implies `PinchTransportEssential` and the previous chapter's residuals imply
`CountedPinch`, the sharp push-off is *necessary* for every one of the family-based residuals of the
ladder: `CountedPinchSweep`, `CountedStep2`, and the sibling chapter's `PinchInputCounting`. -/

theorem pinchTransportEssential_of_countedPinchSweep
    (h : Work.PinchCounted.CountedPinchSweep) : PinchTransportEssential :=
  pinchTransportEssential_of_countedPinch (Work.PinchCounted.countedPinch_of_countedPinchSweep h)

theorem pinchTransportEssential_of_countedStep2 (h : Work.PinchCounted.CountedStep2) :
    PinchTransportEssential :=
  pinchTransportEssential_of_countedPinch (Work.PinchCounted.countedPinch_of_countedStep2 h)

end

end Work.PinchFamily
