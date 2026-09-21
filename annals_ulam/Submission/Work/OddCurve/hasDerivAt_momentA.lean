import Mathlib
import Submission.Work.OddCurve.Defs
import Submission.Work.OddCurve.ContinuousProfile
import Submission.Work.OddCurve.hasDerivAt_integral_rad_general
import Submission.Work.OddCurve.moment_eqs_eq_integral_Icc
import Submission.Work.OddCurve.rad_nonpos_outside

namespace Work.OddCurve

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- **The moment integral `(A)` of the odd case is differentiable in the slope**, with the
derivative obtained by differentiating under the integral sign and letting the moving endpoints
`-(x s)`, `y s` contribute nothing.

The two endpoints sit exactly on the cutting line (the profile is recovered from the curve), so
the radicand `rad h f s t = f t ^ 2 - (s * t + h s) ^ 2` vanishes there; consequently the boundary
terms of the transport formula drop out and the derivative of `s ↦ ∫_{-x s}^{y s}` is the
integral of the pointwise derivative over the section.

The route taken here is short: the section integral is first replaced by the *fixed* interval
integral over `[-1,1]` (the envelope profile vanishes outside `[-1,1]`, so the two integrals agree
for every slope `u > 0` near `s`), the fixed-interval integral is differentiated with
`Work.OddCurve.hasDerivAt_integral_rad_general`, and the resulting kernel — which itself vanishes
outside the section because `rad ≤ 0` there — is transported back to `[-(x s), y s]`. -/
theorem hasDerivAt_momentA {n : ℕ} (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y) {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun u : ℝ => Work.OddCurve.momentA n h x y (Work.OddEnvelope.envelopeProfile h x y) u)
      (∫ t in (-(x s))..(y s),
        -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
          Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t)) s := by
  have hf : Continuous (Work.OddEnvelope.envelopeProfile h x y) := continuous_envelopeProfile H
  -- `h` is differentiable on a neighbourhood of `s` (it is smooth on `(0,∞)` and `s > 0`).
  have hh : ∀ᶠ u : ℝ in nhds s, DifferentiableAt ℝ h u := by
    have hd : DifferentiableOn ℝ h (Set.Ioi (0 : ℝ)) :=
      H.smooth_h.differentiableOn (by simp)
    filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
    exact hd.differentiableAt (isOpen_Ioi.mem_nhds hu)
  -- Differentiate the moment integral over the *fixed* interval `[-1,1]`.
  have hfixed : HasDerivAt
      (fun u : ℝ => ∫ t in (-1 : ℝ)..1,
        Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) u t ^ n *
          Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) u t))
      (∫ t in (-1 : ℝ)..1,
        -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
          Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t)) s :=
    hasDerivAt_integral_rad_general (n := n) (h := h)
      (f := Work.OddEnvelope.envelopeProfile h x y) (a := -1) (b := 1) (s := s)
      hn (by norm_num) hh hf
  -- The derivative kernel vanishes outside the cut section.
  have hzero : ∀ t : ℝ, t ≤ -(x s) ∨ y s ≤ t →
      -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
        Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ (n - 1) *
        Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t) = 0 := by
    intro t ht
    rw [Real.sqrt_eq_zero_of_nonpos (rad_nonpos_outside H hs ht), mul_zero]
  have hx1 : x s ≤ 1 := le_of_lt (H.toChordCurve_x.lt_one hs)
  have hy1 : y s ≤ 1 := le_of_lt (H.toChordCurve_y.lt_one hs)
  have hx0 : 0 < x s := H.toChordCurve_x.pos hs
  have hy0 : 0 < y s := H.toChordCurve_y.pos hs
  -- Transport the fixed interval back to the section `[-(x s), y s]`.
  have hker : (∫ t in (-1 : ℝ)..1,
        -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
          Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t))
      = ∫ t in (-(x s))..(y s),
        -(2 * (n : ℝ) + 1) * (s * t + h s) * (t + deriv h s) *
          Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t ^ (n - 1) *
          Real.sqrt (Work.OddCurve.rad h (Work.OddEnvelope.envelopeProfile h x y) s t) :=
    intervalIntegral_eq_of_eq_zero_outside (a := -1) (b := 1) (c := -(x s)) (d := y s)
      (by linarith) (by linarith) (by linarith)
      (fun t ht => hzero t (Or.inl ht)) (fun t ht => hzero t (Or.inr ht))
  rw [hker] at hfixed
  -- Near `s` the moment integral is the fixed-interval integral.
  refine hfixed.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
  exact (moment_eqs_eq_integral_Icc n H hu (a := -1) (b := 1)
    (by have := H.toChordCurve_x.lt_one hu; linarith)
    (le_of_lt (H.toChordCurve_y.lt_one hu))).1

end

end Work.OddCurve
