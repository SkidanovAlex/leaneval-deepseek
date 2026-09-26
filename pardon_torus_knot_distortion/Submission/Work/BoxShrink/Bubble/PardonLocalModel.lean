import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.BoxShrink.Bubble.Corrected

/-!
# Pardon's own local model: a change of dimension at most one, plus the dichotomy

The counterexample (`Work.BoxShrink.Bubble.standard_counterexample`) shows that the local models
used by `Work.SurgeryInvariance.SweepLoops` — `RegionEquivalent` and `SurgeryStepZero` — are
**strictly stronger** than Pardon's: both preserve the winding span *exactly*, whereas Pardon's
proof of Lemma `spherefamily` only uses that a single surgery changes the dimension of
`im(H₁(F ∩ int S_t; ℚ) → H₁(F; ℚ))` by *at most one*, together with his dichotomy

  `dim im(H₁(F ∩ int S_t) → H₁(F)) ∈ {0, 2g}`  (equation (1) of the paper),

i.e. in the loop-level language of this development,

  `WindingSpan P (F ∩ int S_t) = ⊥ ∨ WindingSpan P (F ∩ int S_t) = ⊤`.

Since a `⊔` of a `⊥` or a line with another submodule of `ℚ²` is never `⊤` unless one summand is,
a change of dimension at most one which takes only the two values `⊥` and `⊤` must preserve `⊥`.

The *definitions* of the corrected local model (`SurgeryStepSmall`, `PardonDichotomy`,
`SweepLoopsSmall`, `PinchDatum`, `PardonPinchInput`, `BubbleInputPardon`) are in
`Work.BoxShrink.Bubble.HalfDefs`, so that they can be imported by the files that still name the
false field (see `MIGRATION.md`); this file records the local-model theorem (Pardon's dimensional
argument) and the consistency of the corrected input with the old one:

* `Work.BoxShrink.Bubble.SurgeryStepSmall` — Pardon's local move: the region gains or loses an open
  piece `Z` of the surface with `WindingSpan P Z ≠ ⊤` (dimension at most one);
* `Work.BoxShrink.Bubble.PardonDichotomy` — Pardon's dichotomy;
* `Work.BoxShrink.Bubble.bot_iff_of_surgeryStepSmall` — with the dichotomy, a small step preserves
  the vanishing of the winding span (and hence "carries an essential loop or not");
* `Work.BoxShrink.Bubble.SweepLoopsSmall` — a one-parameter family with Pardon's local models and
  the dichotomy at every parameter, and `SweepLoopsSmall.containsEssentialLoop_iff` /
  `SweepLoopsSmall.containsEssentialLoop_of_lt_one` — Pardon's Lemma `spherefamily` up to the
  pinching parameter;
* `Work.BoxShrink.Bubble.PinchDatum` — **the corrected isolated input of the pinch**: the family of
  regions of the box/plane configuration, with Pardon's local models, the dichotomy, and the two
  endpoint regions; and `Work.BoxShrink.Bubble.bubbleHalf_of_pinchDatum` — Pardon's Lemma 3
  (`doublebubble`) from it.  The whole shrinking step is then
  `Work.BoxShrink.Bubble.pushOffHalf_of_pardonPinchInput` +
  `Work.BoxShrink.Bubble.crux_of_pushOffHalf`;
* the two interfaces are consistent: a `Work.BoxShrink.Core.BubbleSweep` with the dichotomy at the
  region inside the box gives a `PinchDatum` (`pinchDatum_of_bubbleSweep`), so the corrected input
  is not refuted by the counterexample to `BubbleSweep` — what is missing is exactly the
  *dichotomy*, i.e. the surface-theoretic input that Pardon obtains from the counting hypothesis
  (`Working.InnermostDisk`/`Work.BoxShrink.Core.Counting` territory), not any statement about
  winding spans alone.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Consistency: the old local models give the new ones (given the dichotomy) -/

/-- **Every `BubbleSweep` with the dichotomy at the initial region gives a pinch datum.**  So the
corrected input is implied by the (false) double-bubble family of the library *plus* the dichotomy:
what the counterexample refutes is the family, not the corrected input. -/
def pinchDatum_of_bubbleSweep {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (B : Work.BoxShrink.Core.BubbleSweep P s c σ u)
    (hdich : PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ)) :
    PinchDatum P s c σ u where
  sweep :=
    { region := B.sweep.region
      exc := B.sweep.exc
      regular := B.sweep.regular
      surgery := fun t ht => by
        obtain ⟨ε, hε, hstep⟩ := B.sweep.surgery t ht
        exact ⟨ε, hε, fun s hs =>
          (hstep s hs).imp (fun h => surgeryStepSmall_of_surgeryStepZero h) id⟩
      dichotomy := fun t _ => by
        have h := B.sweep.windingSpan_eq t
        rw [B.zero] at h
        show Work.SurgeryInvariance.WindingSpan P (B.sweep.region t) = ⊥ ∨
          Work.SurgeryInvariance.WindingSpan P (B.sweep.region t) = ⊤
        rw [h]; exact hdich }
  zero := B.zero
  one := B.one
  pinch := by
    by_cases h1 : (1 : ℝ) ∈ B.sweep.exc
    · obtain ⟨ε, hε, hstep⟩ := B.sweep.surgery 1 h1
      refine ⟨1 - ε / 2, by linarith, ?_⟩
      have hmem : |(1 - ε / 2) - 1| < ε := by
        rw [abs_lt]; constructor <;> linarith
      have hdich' : PardonDichotomy P (B.sweep.region (1 - ε / 2)) := by
        have h := B.sweep.windingSpan_eq (1 - ε / 2)
        rw [B.zero] at h
        show Work.SurgeryInvariance.WindingSpan P (B.sweep.region (1 - ε / 2)) = ⊥ ∨
          Work.SurgeryInvariance.WindingSpan P (B.sweep.region (1 - ε / 2)) = ⊤
        rw [h]; exact hdich
      rcases hstep (1 - ε / 2) hmem with h | h
      · exact containsEssentialLoop_of_surgeryStepSmall (surgeryStepSmall_of_surgeryStepZero h)
          hdich'
      · intro hc
        have hspan : Work.SurgeryInvariance.WindingSpan P (B.sweep.region (1 - ε / 2)) ≠ ⊥ :=
          (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hc
        rw [← Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq h] at hspan
        exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P (B.sweep.region 1)).mp hspan
    · obtain ⟨ε, hε, -, hequiv⟩ := B.sweep.regular 1 h1
      refine ⟨1 - ε / 2, by linarith, ?_⟩
      have hmem : |(1 - ε / 2) - 1| < ε := by
        rw [abs_lt]; constructor <;> linarith
      have h := hequiv (1 - ε / 2) hmem
      intro hc
      have hspan : Work.SurgeryInvariance.WindingSpan P (B.sweep.region (1 - ε / 2)) ≠ ⊥ :=
        (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hc
      rw [← Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq h] at hspan
      exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P (B.sweep.region 1)).mp hspan

/-- **The old field plus the dichotomy gives the corrected input.** -/
def pardonPinchInput_of_bubbleSweepAll
    (hb : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
      (u : ℝ), ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Core.BubbleSweep P s c σ u)
    (hdich : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
      (u : ℝ), PardonDichotomy P (Work.BoxShrink.Core.boxRegion P s c σ)) :
    PardonPinchInput :=
  fun P s c σ u hS hZ => pinchDatum_of_bubbleSweep (hb P s c σ u hS hZ) (hdich P s c σ u)

/-- **The double-bubble core from the Pardon-faithful structure**: the exact analogue of
`Work.BoxShrink.Core.cruxCore_of_bubbleInput`. -/
theorem cruxCore_of_bubbleInputPardon (hin : BubbleInputPardon) :
    ∀ p q : ℕ, Work.BoxShrink.CruxCore p q :=
  cruxCore_of_pushOffHalf hin.cleansInDisc (pushOffHalf_of_pardonPinchInput hin.bubble)

/-- **The shrinking step from the Pardon-faithful structure.** -/
theorem crux_of_bubbleInputPardon (hin : BubbleInputPardon)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  crux_of_pushOffHalf hin.cleansInDisc (pushOffHalf_of_pardonPinchInput hin.bubble) hclean hae

end

end Work.BoxShrink.Bubble
