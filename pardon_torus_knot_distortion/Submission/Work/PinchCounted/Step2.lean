import Submission.Work.PinchCounted.Span
import Submission.Work.PinchCounted.exists_sweepLoops_of_countedSweep

/-!
# Pardon's Step 2 as the residual of the counted form

`Assemble.lean` names Pardon's Step 2 as data (`CountedSweep`: the pinching family together with its
intermediate spheres, their cleanings and their counts, and the local moves whose changed pieces have
their loops on those spheres) and states the residual `CountedStep2`: *that datum exists at every
configuration carrying the counting of the crux*.

This module closes the loop: the datum is converted to the library's sweep
(`Work.PinchCounted.exists_sweepLoops_of_countedSweep`, delegated), the two endpoint data turn it
into a `Work.PinchCounted.PinchSweep`, and `bubbleHalf_of_pinchSweep` gives Pardon's Lemma 3
conclusion — hence `Work.BoxShrink.Pinch.CountingHalf`.

`CountedStep2` is the weakest residual of this chapter: unlike `CountedPinchSweep` it does not ask
for the span-preserving local models, only for the geometric mechanism that produces them (Pardon's
Lemma 2 at the intermediate spheres, `Counting.windingSpan_eq_bot_of_subset_of_count`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchCounted

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {β : Work.CoreTopology.ClosedCurve P}

/-- **A `CountedSweep` with the two endpoint data is Pardon's pinch.**  The endgame is not a
hypothesis here: the sweep's local models are span-preserving (`SurgeryStepZero`), so the span is
constant along the family and the conclusion is a monotonicity statement. -/
theorem pinchSweep_of_countedSweep {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (D : CountedSweep P β) (zero : D.region 0 = Work.BoxShrink.Core.boxRegion P s c σ)
    {Z : Set R3} (hZopen : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hZspan : Work.SurgeryInvariance.WindingSpan P Z = ⊥)
    (hZdisj : Disjoint (PinchSweep.halves P s c σ u) Z)
    (one : D.region 1 = PinchSweep.halves P s c σ u ∪ Z) :
    Nonempty (PinchSweep P s c σ u) := by
  obtain ⟨S', hS'⟩ := exists_sweepLoops_of_countedSweep D
  exact ⟨{ sweep := S'
           zero := by rw [hS']; exact zero
           Z := Z
           Z_open := hZopen
           Z_span := hZspan
           Z_disj := hZdisj
           one := by rw [hS']; exact one }⟩

/-- **The counted residual of Pardon's Step 2 gives the counted residual of the pinch.** -/
theorem countedPinchSweep_of_countedStep2 (h : CountedStep2) : CountedPinchSweep :=
  fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
    let ⟨D, hzero, Z, hZopen, hZspan, hZdisj, hone⟩ :=
      h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    pinchSweep_of_countedSweep (β := Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)) D hzero hZopen hZspan hZdisj hone

/-- **Pardon's Lemma 3 in the counted form, from Pardon's Step 2.** -/
theorem countingHalf_of_countedStep2 (h : CountedStep2) : Work.BoxShrink.Pinch.CountingHalf :=
  countingHalf_of_countedPinchSweep (countedPinchSweep_of_countedStep2 h)

/-- **Pardon's shrinking step from Pardon's Step 2.** -/
theorem cruxCore_of_countedStep2 (h : CountedStep2) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  Work.BoxShrink.cruxCore_of_countingHalf (countingHalf_of_countedStep2 h)

/-- **Pardon's theorem from Pardon's Step 2 and his cut-and-paste.** -/
theorem pardon_torus_knot_distortion_of_countedStep2 (h : CountedStep2)
    (hpush : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.pardon_torus_knot_distortion_of_classicalInputs
    ⟨hpush, Or.inl (countingHalf_of_countedStep2 h)⟩

end

end Work.PinchCounted
