import Submission.Work.PinchCounted.Span
import Submission.Work.PinchCounted.Counting
import Submission.Work.PinchCounted.Instances
import Submission.Work.BoxShrink.Pinch.SliceSpanStep

/-!
# The counted form of Pardon's Lemma 3: the reductions, and the two routes compared

## The reductions

Every statement in this file ends in `Work.BoxShrink.Pinch.CountingHalf`, hence (through
`Work.BoxShrink.cruxCore_of_countingHalf`, `Work.BoxShrink.boxShrink_of_countingHalf` and the
ledger) in the challenge `Submission.pardon_torus_knot_distortion`.

| residual | module | reduction |
|---|---|---|
| `CountedPinchSweep` | `Counted.lean` | `countingHalf_of_countedPinchSweep` (via `bubbleHalf_of_pinchSweep`) |
| `Work.BoxShrink.Pinch.PinchInputCounting` (sibling chapter) | `Counted.lean` | `countingHalf_of_pinchInputCounting` |
| `CountedSpanPushOff` | `Span.lean` | `countingHalf_of_countedSpanPushOff` |
| `CountedCollarPushOff` | this module | `countingHalf_of_countedCollarPushOff` (via `bubbleHalf_of_collarPushOff`) |

The first two are *existence statements of Pardon's pinching family*; the last two are span-level
statements (the collar and the weakest span bound).  `CountedPinchSweep` implies
`CountedSpanPushOff` (`countedSpanPushOff_of_countedPinchSweep`) and `CountedSpanPushOff` implies
`CountingHalf`; the collar form is the shape in which Pardon's proof produces the span bound (the
collar's loops are routed through the necks of the pinching spheres, and each neck lies in an
intermediate trace which meets the knot fewer than `I(F,β)` times).

## The two routes, and a correction to the record

`Work.BoxShrink.Pinch.CountingHalf` and `Work.BoxShrink.Pinch.SmoothHalfS` differ in their
hypotheses: `SmoothHalfS` assumes only that the sphere trace and the slice carry no essential loop,
whereas `CountingHalf` carries the whole counting datum of the crux.  The counting *does* imply the
two inessentiality hypotheses (`sphereTrace_inessential_of_counts`, and
`sliceTrace_inessential_of_counts` for the slice), but the derivation of the **slice** one requires
the *planar* innermost input `CleansInSphere (cutDisc s c σ u)`, which the workspace has only for
almost every plane level (`Work.PlaneSlice.aeCleansPardonSlice`) — the slice of the open box is not
transverse in the sense of `Work.Smooth.Plane.TransversePlane` at any level at which a level circle
crosses the boundary of the box (`Work.PlaneSlice.not_ae_transversePlane_pardonSlice`).  With that
input available:

* `countingHalf_of_smoothHalfS_planar : (∀ …, CleansInSphere (torus ψ) (cutDisc s c σ u)) →
  SmoothHalfS → CountingHalf` — the counted form follows from the uncounted one;
* `countingHalf_of_pinchNoJump_planar : (∀ …, CleansInSphere (torus ψ) (cutDisc s c σ u)) →
  Equation1Input → BoxSliceNice → PinchNoJump → CountingHalf` — the counted form follows from the
  *sharpest* residual of the sibling chapter, in its one-sided dimension form.

Both are *conditional*, and deliberately so: they record exactly what a proof of `CountingHalf`
would need in addition to the sibling chapter's development (the planar innermost input at the given
level).  Pardon's own proof needs no such input: it applies Lemma 2 to the intermediate *spheres*
of the pinching family, never to the slicing disc.  That is the precise sense in which
`CountingHalf` is *more* than `SmoothHalfS`: not through the two endpoint hypotheses, but through the
span-preserving local models that his count supplies at the intermediate spheres — which is what
`PinchSweep` records.

**Correction.**  `SmoothHalfS` is **not** refuted by the workshop's counterexample: at the standard
torus with the box `s = 3/2`, `c = 0`, `σ = swap 1 2`, `u = 0` (the configuration at which Pardon's
Lemma 3 conclusion *fails*, `Work.BoxShrink.Pinch.BubbleHalfRefuted`) the hypothesis
`¬ ContainsEssentialLoop (sphereSet c σ s)` is **false**: the sphere trace carries the curve
`θ ↦ torusMap θ (tracePhi θ)` of winding `(1,0)` (`Work.BoxShrink.Pinch.SphereTraceEssential`).
What *is* refuted at scale is the **span** form: at `s = 5/2` both endpoint hypotheses hold
(`Work.BoxShrink.Bubble.cex_not_containsEssentialLoop_sphereSet`,
`…_sliceRegion`), the conclusion of Pardon's Lemma 3 holds
(`Work.BoxShrink.Bubble.bubbleHalf_cex`), and yet the span bound
`W(boxRegion) ≤ W(upperRegion ∪ lowerRegion)` **fails**
(`Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`).  See `Refute.lean` for the two consequences
recorded in this chapter.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

/-! ## The collar form of the counted residual -/

/-- **The counted residual in collar form**: at every configuration carrying the counting data of the
crux, there is a piece `X` of the surface of vanishing winding span (the collar of the slice) such
that every loop of the region inside the box lies either in one of the two half-regions or in `X`.

This is the shape in which Pardon's proof produces the span bound: the intermediate spheres'
traces have vanishing span *because* they meet the knot fewer than `I(F,β)` times
(`windingSpan_eq_bot_of_subset_of_count`, with Pardon's inequality
`|S_t ∩ β| ≤ |S ∩ β| + 2|D ∩ β|` supplying the count at the intermediate spheres), and the collar is
the union of the changed pieces. -/
def CountedCollarPushOff : Prop :=
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
          CollarPushOff (Work.Smooth.Morse.torus ψ) s c σ u

/-- **The counted residual in collar form gives Pardon's Lemma 3 in the counted form.** -/
theorem countingHalf_of_countedCollarPushOff (h : CountedCollarPushOff) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    bubbleHalf_of_collarPushOff
      (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)

/-- **The collar residual gives the span residual.** -/
theorem countedSpanPushOff_of_countedCollarPushOff (h : CountedCollarPushOff) :
    CountedSpanPushOff :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    windingSpan_le_halves_of_collarPushOff
      (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)

/-! ## The uncounted route, made explicit

Both theorems below assume, in addition to the sibling chapter's input, the *planar* innermost input
at the levels of the counted configuration.  It is the only thing standing between the sibling
chapter's residuals and `CountingHalf`, and it is what the counted form of Pardon's Lemma 3 does
without.
-/

/-- **`CountingHalf` from `SmoothHalfS`**, given the planar innermost input at every level. -/
theorem countingHalf_of_smoothHalfS_planar
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h : Work.BoxShrink.Pinch.SmoothHalfS) : Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    h ψ s c σ u
      (sphereTrace_inessential_of_counts p q hp hq hc ψ K hd himg hsmall (lt_trans hr hrs) c σ
        hslice hcl hS)
      (sliceTrace_inessential_of_counts p q hp hq hc ψ K hd himg hsmall (lt_trans hr hrs) c σ u
        (hcleanD ψ s c σ u) hU)

/-- **`CountingHalf` from the sibling chapter's sharpest residual** (`PinchNoJump`), given the
planar innermost input at every level and the two classical inputs of that chapter
(`Equation1Input`: Pardon's equation (1), the classification of compact surfaces; `BoxSliceNice`:
Sard plus the classification of compact `1`-manifolds). -/
theorem countingHalf_of_pinchNoJump_planar
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Work.BoxShrink.Pinch.Equation1Input) (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hstep : Work.BoxShrink.Pinch.PinchNoJump) : Work.BoxShrink.Pinch.CountingHalf :=
  countingHalf_of_smoothHalfS_planar hcleanD
    (Work.BoxShrink.Pinch.smoothHalfS_of_pinchNoJump h1 hnice hstep)

/-! ## The end-to-end statements -/

/-- **Pardon's shrinking step, from the collar form of the counted residual.** -/
theorem cruxCore_of_countedCollarPushOff (h : CountedCollarPushOff) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_countedCollarPushOff h)

/-- **Pardon's shrinking step, from the span form of the counted residual.** -/
theorem cruxCore_of_countedSpanPushOff (h : CountedSpanPushOff) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_countedSpanPushOff h)

/-- **Pardon's theorem, from the collar form of the counted residual and his cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_countedCollarPushOff (h : CountedCollarPushOff)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_countedCollarPushOff h)⟩

/-- **Pardon's theorem, from the span form of the counted residual and his cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_countedSpanPushOff (h : CountedSpanPushOff)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_countedSpanPushOff h)⟩

end

end Work.PinchCounted
