import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleIntegral_logDeriv_eq_zero_of_ne_zero

open Filter
open scoped Topology

namespace Commons.Analysis.Complex

theorem circleIntegral_logDeriv_eq_of_center_factor {f G : ℂ → ℂ} {c : ℂ} {R R' : ℝ} {k : ℕ}
    (hR : 0 < R) (hRR : R < R') (hk : 1 ≤ k)
    (hf : ∀ z ∈ Metric.ball c R', AnalyticAt ℂ f z)
    (hG : ∀ z ∈ Metric.ball c R', AnalyticAt ℂ G z)
    (hfac : ∀ z ∈ Metric.ball c R', f z = (z - c) ^ k * G z)
    (hGne : ∀ z ∈ Metric.closedBall c R, G z ≠ 0) :
    (∮ z in C(c, R), logDeriv f z) = (2 * Real.pi * Complex.I) * (k : ℂ) := by
  -- `G` is analytic on the closed ball of radius `R`.
  have hGan : ∀ z ∈ Metric.closedBall c R, AnalyticAt ℂ G z :=
    fun z hz => hG z (Metric.closedBall_subset_ball hRR hz)
  -- Pointwise identity `f'/f = k/(z-c) + G'/G` on the circle.
  have hpoint : ∀ z ∈ Metric.sphere c R,
      logDeriv f z = (k : ℂ) * (z - c)⁻¹ + logDeriv G z := by
    intro z hz
    have hdist : dist z c = R := Metric.mem_sphere.mp hz
    have hzc : z ≠ c := by
      intro h; rw [h, dist_self] at hdist; linarith
    have hz_ball : z ∈ Metric.ball c R' := by
      rw [Metric.mem_ball, hdist]; exact hRR
    have hz_closed : z ∈ Metric.closedBall c R := by
      rw [Metric.mem_closedBall, hdist]
    have hGz : G z ≠ 0 := hGne z hz_closed
    have hfz : f z = (z - c) ^ k * G z := hfac z hz_ball
    have h_eq_nhds : f =ᶠ[𝓝 z] (fun w : ℂ => (w - c) ^ k * G w) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz_ball] with w hw
      exact hfac w hw
    have hlog_eq : logDeriv f z = logDeriv (fun w : ℂ => (w - c) ^ k * G w) z := by
      rw [logDeriv_apply, logDeriv_apply, h_eq_nhds.deriv_eq, hfz]
    rw [hlog_eq]
    have hpow_ne : (z - c) ^ k ≠ 0 := pow_ne_zero k (sub_ne_zero.mpr hzc)
    have hdiff_pow : DifferentiableAt ℂ (fun w : ℂ => (w - c) ^ k) z := by fun_prop
    have hGdiff : DifferentiableAt ℂ G z := (hG z hz_ball).differentiableAt
    have hstep1 : logDeriv (fun w : ℂ => (w - c) ^ k * G w) z
        = logDeriv (fun w : ℂ => (w - c) ^ k) z + logDeriv G z :=
      logDeriv_mul (f := fun w : ℂ => (w - c) ^ k) (g := G) z hpow_ne hGz hdiff_pow hGdiff
    rw [hstep1]
    have hbase : logDeriv (fun w : ℂ => w - c) z = 1 / (z - c) := by
      have hd : deriv (fun w : ℂ => w - c) z = 1 := by
        rw [show (fun w : ℂ => w - c) = (fun w : ℂ => (id : ℂ → ℂ) w - c) from rfl]
        rw [deriv_sub_const (f := (id : ℂ → ℂ)) (x := z) c]
        simp
      rw [logDeriv_apply, hd, one_div]
    have hstep2 : logDeriv (fun w : ℂ => (w - c) ^ k) z = (k : ℂ) * (1 / (z - c)) := by
      have h := logDeriv_fun_pow (f := fun w : ℂ => w - c) (x := z) (by fun_prop) k
      rw [hbase] at h
      exact h
    rw [hstep2, one_div]
  -- Integrability of both summands on the circle.
  have hA : CircleIntegrable (fun z : ℂ => (k : ℂ) * (z - c)⁻¹) c R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine continuousOn_const.mul ?_
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    intro z hz
    have hdist : dist z c = R := Metric.mem_sphere.mp hz
    have hzc : z ≠ c := by
      intro h; rw [h, dist_self] at hdist; linarith
    exact sub_ne_zero.mpr hzc
  have hB : CircleIntegrable (fun z : ℂ => logDeriv G z) c R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    intro z hz
    have hz_closed : z ∈ Metric.closedBall c R := Metric.sphere_subset_closedBall hz
    have hzan : AnalyticAt ℂ G z := hGan z hz_closed
    have hzne : G z ≠ 0 := hGne z hz_closed
    have hc : ContinuousAt (fun w : ℂ => deriv G w / G w) z :=
      hzan.deriv.continuousAt.div hzan.continuousAt hzne
    simpa only [logDeriv_apply] using hc.continuousWithinAt
  -- Vanishing of the `G'/G` integral.
  have hGzero : (∮ z in C(c, R), logDeriv G z) = 0 :=
    circleIntegral_logDeriv_eq_zero_of_ne_zero hR hGan hGne
  calc
    (∮ z in C(c, R), logDeriv f z)
        = ∮ z in C(c, R), ((k : ℂ) * (z - c)⁻¹ + logDeriv G z) :=
          circleIntegral.integral_congr hR.le hpoint
    _ = (∮ z in C(c, R), (k : ℂ) * (z - c)⁻¹) + (∮ z in C(c, R), logDeriv G z) :=
          circleIntegral.integral_add hA hB
    _ = (k : ℂ) * (∮ z in C(c, R), (z - c)⁻¹) + (∮ z in C(c, R), logDeriv G z) := by
          rw [circleIntegral.integral_const_mul]
    _ = (k : ℂ) * (2 * Real.pi * Complex.I) + 0 := by
          rw [circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hR), hGzero]
    _ = (2 * Real.pi * Complex.I) * (k : ℂ) := by ring

end Commons.Analysis.Complex
