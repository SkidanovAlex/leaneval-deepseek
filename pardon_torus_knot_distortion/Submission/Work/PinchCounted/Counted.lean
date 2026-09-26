import Submission.Work.PinchCounted.Defs
import Submission.Work.BoxShrink.Pinch.SliceSpanStep

/-!
# The counted residual, and Pardon's Lemma 3 from it

This module isolates the **counted residual of Pardon's Lemma 3** in its exact geometric form,
`CountedPinchSweep`: at every configuration carrying the counting data of the crux, Pardon's
pinching family of spheres exists, with the *span-preserving* local models that his counting
argument supplies (`Work.PinchCounted.PinchSweep`).

It then proves the two reductions of the challenge to that residual:

* `countingHalf_of_countedPinchSweep : CountedPinchSweep → Work.BoxShrink.Pinch.CountingHalf`
  (the ledger's input), and through it `Work.BoxShrink.CruxCore`, `Submission.BoxShrinkStatement`
  and the challenge itself;
* `countingHalf_of_pinchInputCounting : Work.BoxShrink.Pinch.PinchInputCounting →
  Work.BoxShrink.Pinch.CountingHalf` — the same residual in the vocabulary of the sibling chapter
  `Work.BoxShrink.Pinch` (Pardon's pinch recorded with `SurgeryStepSmall` local models and the
  endgame field).  The two residuals are *different*: `PinchSweep` uses the stronger
  `SurgeryStepZero` local models (which the counting supplies) and needs no endgame field, whereas
  `PinchInputCounting` uses the weaker `SurgeryStepSmall` local models and needs the endgame.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

/-! ## The counted residual -/

/-- **The counted residual of Pardon's Lemma 3.**  Every configuration carrying the counting data
of `Work.BoxShrink.CruxCore` — the knot `K`, the distortion bound `d` with
`countConst · d < min p q`, the swept box sphere together with its count
`|S ∩ β| ≤ 10(1+ε)/ε · d`, the plane level with `|D ∩ β| ≤ 5(1+ε)/ε · d`, and the cut-and-paste
input — carries Pardon's pinching family with span-preserving local models.

This is Pardon's Step 2 (`|S_t ∩ β| ≤ |S ∩ β| + 2|D ∩ β| < I(F,β)` at every intermediate sphere,
hence inessentiality of every changed piece) together with the construction of the family. -/
def CountedPinchSweep : Prop :=
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
          Nonempty (PinchSweep (Work.Smooth.Morse.torus ψ) s c σ u)

/-- **Pardon's Lemma 3 in the counted form, from the counted residual.**  `CountingHalf` is
`CountedPinchSweep` with the pinch replaced by its conclusion. -/
theorem countingHalf_of_countedPinchSweep (h : CountedPinchSweep) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    bubbleHalf_of_pinchSweep
      (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU).some

/-- **Pardon's Lemma 3 in the counted form, from the sibling chapter's counted residual.**  The
input `Work.BoxShrink.Pinch.PinchInputCounting` is Pardon's pinch recorded with his dichotomy local
models (`SurgeryStepSmall`) and the endgame step; it is the residual of the sibling chapter
`Work.BoxShrink.Pinch`. -/
theorem countingHalf_of_pinchInputCounting (h : Work.BoxShrink.Pinch.PinchInputCounting) :
    Work.BoxShrink.Pinch.CountingHalf :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    Work.BoxShrink.Pinch.bubbleHalf_of_pinchFamily
      (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU).some

/-! ## The shrinking step, and the challenge -/

/-- **Pardon's shrinking step from the counted residual.** -/
theorem cruxCore_of_countedPinchSweep (h : CountedPinchSweep) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_countedPinchSweep h)

/-- **Pardon's shrinking step from the sibling chapter's counted residual.** -/
theorem cruxCore_of_pinchInputCounting (h : Work.BoxShrink.Pinch.PinchInputCounting) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_pinchInputCounting h)

/-- **`Submission.BoxShrinkStatement`, from the counted residual** (using the two remaining
classical inputs: the cut-and-paste `PushThroughInnermost` and the almost-everywhere general
position of the box-norm levels). -/
theorem boxShrink_of_countedPinchSweep (h : CountedPinchSweep)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q :=
  Work.BoxShrink.boxShrink_of_crux fun p q =>
    ⟨Work.BoxShrink.cleansDiscsAll_of_pushThrough hpush,
      cruxCore_of_countedPinchSweep h p q,
      Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis⟩

/-- **Pardon's theorem from the counted residual and Pardon's cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_countedPinchSweep (h : CountedPinchSweep)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_countedPinchSweep h)⟩

/-- **Pardon's theorem from the sibling chapter's counted residual and Pardon's cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_pinchInputCounting
    (h : Work.BoxShrink.Pinch.PinchInputCounting)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_pinchInputCounting h)⟩

end

end Work.PinchCounted
