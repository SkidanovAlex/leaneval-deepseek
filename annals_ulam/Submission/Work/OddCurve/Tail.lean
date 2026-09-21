import Submission.Work.OddCurve.Defs
import Submission.Work.OddCurve.tail_moment_eqs

/-!
# The two moment equations on all slopes `0 < s ≤ 1`

The construction of the odd case produces the two moment equations on the transition slopes
`0 < s ≤ 1 - τ` (the paper's Steps 2 and 3, the content of `SmallSlopeCurveExists`).  On the
remaining slopes `1 - τ < s ≤ 1` the chord curve is the semicircle's and `h` vanishes, so the
equations reduce to the ball identity with the constant `refConst n`
(`Work.OddCurve.tail_moment_eqs`).

This file puts the two ranges together: that is the step which turns the transition-slope input into
the consumer's `(0,1]` statement.
-/

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The moment equations on `(0,1]`** from the transition-slope equations `(0, 1-τ]` and the free
semicircle tail `(1-τ, 1]`, with the constant normalised to `refConst n`. -/
theorem momentEqsOn_Ioc_one_of_smallSlopes (n : ℕ) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hz : ∀ s : ℝ, 1 - tau < s → Filter.EventuallyEq (nhds s) h (fun _ : ℝ => 0))
    (hsmall : SmallSlopeEqs n h x y) :
    MomentEqsOn n (refConst n) h x y (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioc 0 1) := by
  obtain ⟨hA, hB⟩ := (smallSlopeEqs_iff n h x y).mp hsmall
  obtain ⟨tA, tB⟩ := tail_moment_eqs n H hz
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · by_cases hle : s ≤ 1 - tau
    · exact hA s hs.1 hle
    · exact tA s ⟨lt_of_not_ge hle, hs.2⟩
  · by_cases hle : s ≤ 1 - tau
    · exact hB s hs.1 hle
    · exact tB s ⟨lt_of_not_ge hle, hs.2⟩

end

end Work.OddCurve
