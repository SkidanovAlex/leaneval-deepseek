import Mathlib
import Submission.Work.OddCurve.const_eq_refConst_of_smallSlope
import Submission.Work.OddEnvelope.Main

namespace Work.OddVolterra.Existence

/-- **The envelope profile is the semicircle on the section of slope `1`.**

`Work.OddCurve.envelopeProfile_eq_semicircle_Icc_tStar` gives the agreement with the semicircle
on `[-a, a]` for every `0 < a ≤ tStar`.  Here `a = profileX 1`, and `profileX 1 ≤ tStar` because
`tStar = profileX (1 - tau)` with `1 - tau = 9/10 < 1` and `profileX` is strictly antitone on
`(0, ∞)`.

This is the hypothesis `hfb` of `Work.OddVolterra.RowIdentity.Setup`: the body section cut by the
slope-`1` line is the unperturbed one. -/
theorem envelopeProfile_eq_semicircle_Icc_profileX1 {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) :
    ∀ t ∈ Set.Icc (-(Work.OddEnvelope.profileX 1)) (Work.OddEnvelope.profileX 1),
      Work.OddEnvelope.envelopeProfile h x y t = Work.OddEnvelope.semicircle t := by
  refine Work.OddCurve.envelopeProfile_eq_semicircle_Icc_tStar H
    (Work.OddEnvelope.profileX_pos 1) ?_
  have hmono := Work.OddEnvelope.profileX_strictAntiOn.antitoneOn
  rw [Work.OddEnvelope.tStar, Work.OddEnvelope.tau]
  exact hmono (show (1 : ℝ) - 1 / 10 ∈ Set.Ioi (0 : ℝ) by norm_num)
    (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num) (by norm_num)

end Work.OddVolterra.Existence
