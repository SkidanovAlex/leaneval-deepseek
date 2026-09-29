import Mathlib
import Submission.Work.TMComp.Kotani.mfun_props

namespace Work.TMComp.Kotani

/-- **Imaginary-part shift identity for the `m`-function** (AJ (M′), `NOTES.md` step L1):
`im m(x+α) = Im E + im m(x) / ‖m(x)‖²`.

Immediate from the covariance relation `m(x+α) = E - pot lam x - 1/m(x)` together with the
one-step imaginary-part identity `step_im_eq`. -/
theorem mfun_im_shift (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) (x : ℝ) :
    (Work.TMComp.Kotani.mfun α lam E (x + α)).im
      = E.im + (Work.TMComp.Kotani.mfun α lam E x).im
          / ‖Work.TMComp.Kotani.mfun α lam E x‖ ^ 2 := by
  have hm0 : mfun α lam E x ≠ 0 := by
    intro h0
    have hpos := MfunProbs.mfun_im_pos α lam hE x
    rw [h0] at hpos; simp at hpos
  rw [MfunProbs.mfun_covariance α lam hE x]
  exact MfunProbs.step_im_eq hm0

end Work.TMComp.Kotani
