import Mathlib
import Submission.Work.A14D.ppc_aux
import Submission.Work.CPull.evp_sympPhi

/-!
# `Work.A14D.evp_deriv_sympY`

The evaluation of the derivative of `sympY = x²/(x−1)` at a point `z` of the open unit disc
equals `dyC z = (z²−2z)/(z−1)²`, the derivative of the analytic function `z ↦ z²/(z−1)`.

Route: `evp (derivative f) z = deriv (evp f) z` on the disc (`Work.A14D.evp_deriv`, using the
polynomial growth of the coefficients of `sympY`), and `evp sympY w = w²/(w−1)` on the disc
(`Work.CPull.evp_sympPhi`).  Hence it suffices to differentiate `w ↦ w²/(w−1)` at `z`.
-/

namespace Work.A14D

theorem evp_deriv_sympY {z : ℂ} (hz : ‖z‖ < 1) :
    Work.CPull.evp (PowerSeries.derivative (R := ℚ) Submission.CDT.sympY) z = Work.A14D.dyC z := by
  obtain ⟨C, hC, k, hk⟩ := Work.A14D.poly_growth_sympY
  rw [Work.A14D.evp_deriv hC hk hz]
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have heq : (fun w : ℂ => Work.CPull.evp Submission.CDT.sympY w)
      =ᶠ[nhds z] (fun w : ℂ => w ^ 2 / (w - 1)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with w hw
    exact (Work.CPull.evp_sympPhi w (by simpa [Metric.mem_ball, dist_zero_right] using hw)).2
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hz1 : z ≠ 1 := by rintro rfl; norm_num at hz
  have h : HasDerivAt (fun w : ℂ => w ^ 2 / (w - 1)) (Work.A14D.dyC z) z := by
    have hnum : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z)
    have hden : HasDerivAt (fun w : ℂ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
    have hd := hnum.div hden (sub_ne_zero.mpr hz1)
    have he : (2 * z * (z - 1) - z ^ 2 * 1) / (z - 1) ^ 2 = Work.A14D.dyC z := by
      rw [Work.A14D.dyC]; ring
    rwa [he] at hd
  exact h.deriv

end Work.A14D
