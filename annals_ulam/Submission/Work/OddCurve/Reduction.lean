import Submission.Work.OddCurve.Tail
import Submission.Work.OddCurve.const_eq_refConst_of_smallSlope

/-!
# The main reduction of the chapter

`SmallSlopeCurveExists n` is the one remaining mathematical input of the odd-dimensional case: for
every sufficiently small flat bump `h` there is a chord curve `(x,y)` with `IsEnvelopeCurve h x y`
and the two moment equations on the *transition* slopes `0 < s ≤ 1 - τ`.  It is what the paper's
Step 2 (the Volterra system `G(s,Z(s)) = ∫_s^1 Θ + Ξ`, NRZ Lemma 8, solved by NRZ's
contraction/implicit-function theorem) together with Step 3 (the spherical Radon transform, or the
leftward continuation of the Volterra solution) produces.

This file proves that `SmallSlopeCurveExists n` implies the consumer's conclusion
`Work.OddCurve.OddCurveExists n`, i.e. the deliverable of the chapter, *verbatim*:
`odd_curve_exists_of_smallSlopeCurveExists` is stated in the exact shape of the consumer's request
(`odd_curve_exists`), with the hypotheses literally as in their statement (support inside
`Ioo (1-2/10) (1-1/10)`, the three `ε`-bounds, flatness at the left edge of the window, `h ≠ 0`).

The mathematical content of the reduction is only the *tail*: on the slopes `1-τ < s ≤ 1` the
chord curve is the semicircle's and `h` vanishes, so `envelopeProfile h x y` is the semicircle
there and both equations reduce to the ball identity with constant `refConst n`
(`Work.OddCurve.tail_moment_eqs`, `Work.OddCurve.momentEqsOn_Ioc_one_of_smallSlopes`).
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The bumps satisfying the consumer's hypothesis list satisfy `IsSmallFlatBump ε`. -/
theorem isSmallFlatBump_of_consumer {ε : ℝ} {h : ℝ → ℝ}
    (hcont : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10)) (1 - (1 / 10)))
    (hb1 : ∀ s : ℝ, |h s| ≤ ε) (hb2 : ∀ s : ℝ, |deriv h s| ≤ ε)
    (hb3 : ∀ s : ℝ, |deriv (deriv h) s| ≤ ε)
    (hflat : ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10) ≤ s →
      s < 1 - 2 * (1 / 10) + η → h s = 0) :
    IsSmallFlatBump ε h :=
  ⟨hcont, hsupp, hb1, hb2, hb3, hflat⟩

/-- **The chapter's main reduction.**  The transition-slope curve (the paper's Steps 2 and 3) gives
the consumer's `OddCurveExists`. -/
theorem oddCurveExists_of_smallSlopeCurveExists (n : ℕ) (H : SmallSlopeCurveExists n) :
    OddCurveExists n := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hbump hne => ?_⟩
  obtain ⟨x, y, hH, hsl⟩ := H' h hbump hne
  exact ⟨refConst n, x, y, hH,
    momentEqsOn_Ioc_one_of_smallSlopes n hH
      (fun s hs => hbump.eventuallyEq_zero_of_gt hs) hsl⟩

/-- **The constant is forced.**  A construction of the transition-slope curve may leave the
constant `C` free: the equations at `s = 1 - τ` (which belong to the transition range) force
`C = refConst n`, because at that slope the chord is exactly the unperturbed part of the profile,
where the value is the ball's.  This is what makes the normalisation in `SmallSlopeEqs` harmless —
and it is why a future construction should aim at the `SmallSlopeCurveExistsC` form. -/
theorem smallSlopeEqs_of_smallSlopeEqsC (n : ℕ) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hsupp : Function.support h ⊆ Set.Ioo (1 - 2 * tau) (1 - tau))
    {C : ℝ} (hEq : SmallSlopeEqsC n C h x y) : SmallSlopeEqs n h x y := by
  have hC : C = refConst n := const_eq_refConst_of_smallSlope n H hsupp hEq
  rw [hC] at hEq
  exact hEq

/-- The transition-slope existence in the free-constant form gives the normalised form. -/
theorem smallSlopeCurveExists_of_smallSlopeCurveExistsC (n : ℕ)
    (H : SmallSlopeCurveExistsC n) : SmallSlopeCurveExists n := by
  obtain ⟨ε, hε, H'⟩ := H
  refine ⟨ε, hε, fun h hbump hne => ?_⟩
  obtain ⟨C, x, y, hIC, hEq⟩ := H' h hbump hne
  exact ⟨x, y, hIC, smallSlopeEqs_of_smallSlopeEqsC n hIC hbump.support_subset hEq⟩

/-- **The deliverable**, in the literal shape of the consumer's request: the transition-slope curve
for every small flat bump yields `∃ C, ∃ x y` with `IsEnvelopeCurve h x y` and the two moment
equations for every `0 < s ≤ 1` (the profile being `Work.OddEnvelope.envelopeProfile h x y` and the
constant `C = Work.OddCurve.refConst n`). -/
theorem odd_curve_exists_of_smallSlopeCurveExists (n : ℕ) (hn : 1 ≤ n)
    (H : SmallSlopeCurveExists n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ ∞ h →
      Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10)) (1 - (1 / 10)) →
      (∀ s : ℝ, |h s| ≤ ε) → (∀ s : ℝ, |deriv h s| ≤ ε) →
      (∀ s : ℝ, |deriv (deriv h) s| ≤ ε) →
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10) ≤ s →
        s < 1 - 2 * (1 / 10) + η → h s = 0) →
      h ≠ 0 →
      ∃ C : ℝ, ∃ x y : ℝ → ℝ,
        Work.OddEnvelope.IsEnvelopeCurve h x y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) s =
            C / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          momentB n h x y (Work.OddEnvelope.envelopeProfile h x y) s = 0) := by
  obtain ⟨ε, hε, Hh⟩ := oddCurveExists_of_smallSlopeCurveExists n H
  refine ⟨ε, hε, fun h hcont hsupp hb1 hb2 hb3 hflat hne => ?_⟩
  have hbump : IsSmallFlatBump ε h := isSmallFlatBump_of_consumer hcont hsupp hb1 hb2 hb3 hflat
  obtain ⟨C, x, y, hH, hme⟩ := Hh h hbump hne
  obtain ⟨hA, hB⟩ :=
    (momentEqsOn_Ioc_iff n C h x y (Work.OddEnvelope.envelopeProfile h x y)).mp hme
  exact ⟨C, x, y, hH, hA, hB⟩

/-- **The deliverable, written out.**  `odd_curve_exists_of_smallSlopeCurveExists` with both
moment integrals spelled textually (no reference to `momentA`/`momentB`): this is the exact shape of
the consumer's `odd_curve_exists`, with the profile `P` realised as
`Work.OddEnvelope.envelopeProfile h x y`.  The proof is an `exact` (the two spellings are
definitionally equal), which makes the shape agreement machine-checked. -/
theorem odd_curve_exists_of_smallSlopeCurveExists_written (n : ℕ) (hn : 1 ≤ n)
    (H : SmallSlopeCurveExists n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ ∞ h →
      Function.support h ⊆ Set.Ioo (1 - 2 * (1 / 10)) (1 - (1 / 10)) →
      (∀ s : ℝ, |h s| ≤ ε) → (∀ s : ℝ, |deriv h s| ≤ ε) →
      (∀ s : ℝ, |deriv (deriv h) s| ≤ ε) →
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * (1 / 10) ≤ s →
        s < 1 - 2 * (1 / 10) + η → h s = 0) →
      h ≠ 0 →
      ∃ C : ℝ, ∃ x y : ℝ → ℝ,
        Work.OddEnvelope.IsEnvelopeCurve h x y ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ n *
              Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2)) =
            C / Real.sqrt (1 + s ^ 2)) ∧
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          (∫ t in (-x s)..(y s),
            (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) *
              Real.sqrt (Work.OddEnvelope.envelopeProfile h x y t ^ 2 - (s * t + h s) ^ 2) *
              (t + deriv h s)) = 0) :=
  odd_curve_exists_of_smallSlopeCurveExists n hn H

end

end Work.OddCurve
