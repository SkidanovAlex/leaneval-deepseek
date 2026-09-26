import Submission.Work.PinchCounted.Local

/-!
# The dimension form of the residual: Pardon's `spherefamily` invariant

Pardon's Lemma 1 (`spherefamily`) does not, as he states it, equate the subspaces
`W(F ∩ int S_t) ≤ ℚ² = H₁(T²;ℚ)` along the pinching family: it proves that the *dimension*
`dim_ℚ im(H₁(F ∩ int S_t;ℚ) → H₁(F;ℚ))` is constant (it equals `2g` when `F ∩ int S_t` has a
component of genus `g`, and `0` otherwise).  The workspace's `Work.SurgeryInvariance.SweepLoops`
sharpens this to the equality of the subspaces (`windingSpan_eq`), which is what the residuals of
this chapter use.

This module records the *dimension* form as a residual of its own, `Work.PinchCounted.CountedDim`:
at every counted configuration,
`finrank W(boxRegion) = finrank W(halves)`.

It is **equivalent** to the span containment `CountedSpanPushOff` of `Span.lean`
(`countedSpanPushOff_iff_countedDim`): the span containment gives the dimension equality directly,
and conversely the two half-regions lie in the box region, so `W(halves) ≤ W(boxRegion)`, and a
containment with equal finite dimension is an equality (`Submodule.eq_of_le_of_finrank_eq`).  Either
form implies `CountingHalf`.  Recording both lets a prover of the pinch aim at whichever of Pardon's
two statements — his invariant, or the span containment — is convenient.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The dimension form of the counted residual.**  At every configuration carrying the counting
data of the crux, Pardon's invariant `dim_ℚ im(H₁(F ∩ int S_t;ℚ) → H₁(F;ℚ))` has the same value at
the two ends of the pinch: the box region and the union of the two half-regions. -/
def CountedDim : Prop :=
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
          Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) =
            Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (PinchSweep.halves (Work.Smooth.Morse.torus ψ) s c σ u))

/-- **The span containment implies the dimension equality**: a containment with equal finite
dimension is an equality. -/
theorem countedDim_of_countedSpanPushOff (h : CountedSpanPushOff) : CountedDim :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU => by
    have hmono : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (PinchSweep.halves (Work.Smooth.Morse.torus ψ) s c σ u) ≤
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) :=
      Work.SurgeryInvariance.WindingSpan_mono (Work.Smooth.Morse.torus ψ)
        (Set.union_subset (Work.BoxShrink.Core.upperRegion_subset
            (Work.Smooth.Morse.torus ψ) s c σ u)
          (Work.BoxShrink.Core.lowerRegion_subset (Work.Smooth.Morse.torus ψ) s c σ u))
    have heq : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) =
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (PinchSweep.halves (Work.Smooth.Morse.torus ψ) s c σ u) :=
      le_antisymm
        (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)
        hmono
    rw [heq]

/-- **The dimension form gives the span containment** (hence Pardon's Lemma 3 conclusion, hence the
counted form): the two half-regions lie in the box region, so their span is contained in its, and a
containment with equal finite dimension is an equality. -/
theorem countedSpanPushOff_of_countedDim (h : CountedDim) : CountedSpanPushOff :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU => by
    have hmono : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (PinchSweep.halves (Work.Smooth.Morse.torus ψ) s c σ u) ≤
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) :=
      Work.SurgeryInvariance.WindingSpan_mono (Work.Smooth.Morse.torus ψ)
        (Set.union_subset (Work.BoxShrink.Core.upperRegion_subset
            (Work.Smooth.Morse.torus ψ) s c σ u)
          (Work.BoxShrink.Core.lowerRegion_subset (Work.Smooth.Morse.torus ψ) s c σ u))
    exact (Submodule.eq_of_le_of_finrank_eq hmono
      (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU).symm).ge

/-- **Pardon's Lemma 3 from the dimension form.** -/
theorem countingHalf_of_countedDim (h : CountedDim) : Work.BoxShrink.Pinch.CountingHalf :=
  countingHalf_of_countedSpanPushOff (countedSpanPushOff_of_countedDim h)

theorem countedSpanPushOff_iff_countedDim : CountedSpanPushOff ↔ CountedDim :=
  ⟨countedDim_of_countedSpanPushOff, countedSpanPushOff_of_countedDim⟩

/-- **Pardon's shrinking step from the dimension form.** -/
theorem cruxCore_of_countedDim (h : CountedDim) : ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_countedDim h)

/-- **`Submission.BoxShrinkStatement` from the dimension form** (with Pardon's cut-and-paste and
the almost-everywhere general position). -/
theorem boxShrink_of_countedDim (h : CountedDim)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux fun p q =>
    ⟨Work.BoxShrink.cleansDiscsAll_of_pushThrough hpush,
      cruxCore_of_countedDim h p q,
      Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis⟩

/-- **Pardon's theorem from the dimension form and his cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_countedDim (h : CountedDim)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_countedDim h)⟩

end

end Work.PinchCounted
