import Mathlib

namespace Work.Pert.PinLogDev.AxisAux

/-- The principal branch of the complex logarithm is 4-Lipschitz on the closed disk of
radius `3/4` about `1` (where `‖log' z‖ = ‖z‖⁻¹ ≤ 4`). -/
theorem log_sub_log_norm_le {P Q : ℂ} (hP : ‖P - 1‖ ≤ 3 / 4) (hQ : ‖Q - 1‖ ≤ 3 / 4) :
    ‖Complex.log P - Complex.log Q‖ ≤ 4 * ‖P - Q‖ := by
  set s : Set ℂ := Metric.closedBall (1 : ℂ) (3 / 4) with hs
  have hconv : Convex ℝ s := convex_closedBall _ _
  have hPs : P ∈ s := by rw [hs, Metric.mem_closedBall, dist_eq_norm]; exact hP
  have hQs : Q ∈ s := by rw [hs, Metric.mem_closedBall, dist_eq_norm]; exact hQ
  -- Every point of `s` lies in the slit plane, so `log` is (complex) differentiable there.
  have hslit : ∀ x ∈ s, x ∈ Complex.slitPlane := by
    intro x hx
    have hx1 : ‖x - 1‖ < 1 := by
      rw [hs, Metric.mem_closedBall, dist_eq_norm] at hx; linarith
    have := Complex.mem_slitPlane_of_norm_lt_one (z := x - 1) hx1
    simpa using this
  have hdiff : ∀ x ∈ s, DifferentiableAt ℂ Complex.log x := fun x hx =>
    Complex.differentiableAt_log (hslit x hx)
  -- The derivative `1/z` is bounded by `4` on `s`, since `‖z‖ ≥ 1 - 3/4 = 1/4`.
  have hbdd : ∀ x ∈ s, ‖fderiv ℂ Complex.log x‖ ≤ (4 : ℝ) := by
    intro x hx
    have hxge : (1 : ℝ) / 4 ≤ ‖x‖ := by
      have h := norm_sub_norm_le (1 : ℂ) x
      rw [norm_one] at h
      have h2 : ‖(1 : ℂ) - x‖ = ‖x - 1‖ := by rw [← norm_neg, neg_sub]
      rw [h2] at h
      have hxle : ‖x - 1‖ ≤ 3 / 4 := by
        rw [hs, Metric.mem_closedBall, dist_eq_norm] at hx; exact hx
      linarith
    rw [(Complex.hasDerivAt_log (hslit x hx)).hasFDerivAt.fderiv,
      ContinuousLinearMap.norm_toSpanSingleton]
    rw [norm_inv]
    rw [inv_le_comm₀ (by linarith : (0 : ℝ) < ‖x‖) (by norm_num : (0 : ℝ) < 4)]
    norm_num
    exact hxge
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbdd hconv hQs hPs

end Work.Pert.PinLogDev.AxisAux
