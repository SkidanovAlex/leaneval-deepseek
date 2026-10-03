import Mathlib
import Submission.Work.Repel.Koebe.Setup
import Submission.Work.Repel.Koebe.ExteriorWindingDefs
import Submission.Work.Repel.Koebe.Phi_analyticOnNhd_ball
import Submission.Work.Repel.Koebe.Phi_ne_zero
import Submission.Work.Repel.Koebe.logDeriv_Phi_eq
import Submission.Work.Repel.Koebe.circleIntegral_comp_inv
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleIntegral_logDeriv_eq_zero_of_ne_zero

/-!
# The winding number `wind g r ζ = 1` for a map `g` close to the identity at infinity

Let `g` be holomorphic on the exterior `{1 < ‖z‖}` of the unit disc, with `‖g z - z‖ ≤ 1/2` for all
large `‖z‖`, let `1 < r`, and suppose that `g` omits the value `ζ` on the closed exterior
`{r ≤ ‖z‖}`.  Then the winding number of the curve `z ↦ g z` over the circle `‖z‖ = r` about `ζ`,
`wind g r ζ = (2 π i)⁻¹ ∮_{‖z‖ = r} (deriv g z)/(g z - ζ) dz`, equals `1`.

Proof.  Put `Φ v = v * (g v⁻¹ - ζ)` (extended by `1` at `v = 0`), which is holomorphic on the unit
disc by the bound at infinity, and nonvanishing on the closed disc of radius `r⁻¹` by the omission
hypothesis.  Hence the logarithmic derivative `Φ'/Φ` has vanishing circle integral over `‖v‖ = r⁻¹`
(Cauchy–Goursat).  On that circle `logDeriv Φ = 1/v - (v²)⁻¹ (deriv g v⁻¹)/(g v⁻¹ - ζ)`; the first
term integrates to `2πi`, and the substitution `v = w⁻¹` (reversing the orientation) turns the
second into `-∮_{‖w‖=r} (deriv g w)/(g w - ζ)`.  So that last integral equals `2πi`, i.e.
`wind g r ζ = 1`. -/

namespace Work.Repel.Koebe

set_option maxHeartbeats 1000000 in
theorem wind_eq_one {g : ℂ → ℂ} {ζ : ℂ} {r : ℝ} (hr : 1 < r)
    (hg : ∀ z : ℂ, 1 < ‖z‖ → AnalyticAt ℂ g z)
    (hbound : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖g z - z‖ ≤ 1 / 2)
    (hζ : ∀ z : ℂ, r ≤ ‖z‖ → g z ≠ ζ) :
    wind g r ζ = 1 := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hrinv0 : 0 < r⁻¹ := inv_pos.mpr hr0
  have hrinv1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  -- `Φ` is holomorphic on the unit disc and nonvanishing on the closed disc of radius `r⁻¹`
  have han : AnalyticOnNhd ℂ (Phi g ζ) (Metric.ball (0 : ℂ) 1) :=
    Phi_analyticOnNhd_ball hg hbound
  have hclosed : Metric.closedBall (0 : ℂ) r⁻¹ ⊆ Metric.ball (0 : ℂ) 1 := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hv hrinv1
  have hne : ∀ v ∈ Metric.closedBall (0 : ℂ) r⁻¹, Phi g ζ v ≠ 0 := by
    intro v hv
    exact Phi_ne_zero hr0 hζ v (by rwa [Metric.mem_closedBall, dist_zero_right] at hv)
  -- Cauchy–Goursat: the logarithmic derivative integrates to zero
  have harg : circleIntegral (fun v : ℂ => logDeriv (Phi g ζ) v) 0 r⁻¹ = 0 :=
    Commons.Analysis.Complex.circleIntegral_logDeriv_eq_zero_of_ne_zero hrinv0
      (fun v hv => han v (hclosed hv)) hne
  -- bookkeeping on the two circles
  have hne_sph : ∀ v ∈ Metric.sphere (0 : ℂ) r⁻¹, v ≠ 0 := by
    intro v hv h0
    rw [Metric.mem_sphere, dist_zero_right] at hv
    rw [h0, norm_zero] at hv
    exact absurd hv.symm (ne_of_gt hrinv0)
  have hmem_inv : ∀ v ∈ Metric.sphere (0 : ℂ) r⁻¹, v⁻¹ ∈ Metric.sphere (0 : ℂ) r := by
    intro v hv
    rw [Metric.mem_sphere, dist_zero_right] at hv ⊢
    rw [norm_inv, hv, inv_inv]
  have hcont_h : ContinuousOn (fun w : ℂ => deriv g w / (g w - ζ)) (Metric.sphere (0 : ℂ) r) := by
    intro w hw
    have hwn : ‖w‖ = r := by rwa [Metric.mem_sphere, dist_zero_right] at hw
    have hw1 : 1 < ‖w‖ := by rw [hwn]; exact hr
    have hanz : AnalyticAt ℂ g w := hg w hw1
    have hne' : g w - ζ ≠ 0 := sub_ne_zero.mpr (hζ w (le_of_eq hwn.symm))
    exact (hanz.deriv.continuousAt.div (hanz.continuousAt.sub continuousAt_const)
      hne').continuousWithinAt
  -- the pointwise formula for `logDeriv Φ` on the circle `‖v‖ = r⁻¹`
  have hlog : circleIntegral (fun v : ℂ => logDeriv (Phi g ζ) v) 0 r⁻¹
      = circleIntegral
          (fun v : ℂ => 1 / v - (v ^ 2)⁻¹ * (deriv g v⁻¹ / (g v⁻¹ - ζ))) 0 r⁻¹ := by
    refine circleIntegral.integral_congr hrinv0.le fun v hv => ?_
    rw [Metric.mem_sphere, dist_zero_right] at hv
    have hv0 : v ≠ 0 := by
      intro h; rw [h, norm_zero] at hv; exact absurd hv.symm (ne_of_gt hrinv0)
    have hinvnorm : ‖v⁻¹‖ = r := by rw [norm_inv, hv, inv_inv]
    exact logDeriv_Phi_eq hv0 (hg v⁻¹ (by rw [hinvnorm]; exact hr))
      (hζ v⁻¹ (le_of_eq hinvnorm.symm))
  -- circle integrability of the two summands
  have hint1 : CircleIntegrable (fun v : ℂ => 1 / v) 0 r⁻¹ := by
    refine ContinuousOn.circleIntegrable hrinv0.le ?_
    exact ContinuousOn.div continuousOn_const continuousOn_id hne_sph
  have hint2 : CircleIntegrable
      (fun v : ℂ => (v ^ 2)⁻¹ * (deriv g v⁻¹ / (g v⁻¹ - ζ))) 0 r⁻¹ := by
    refine ContinuousOn.circleIntegrable hrinv0.le ?_
    refine ContinuousOn.mul ?_ ?_
    · exact ContinuousOn.inv₀ (continuousOn_id.pow 2) (fun v hv => pow_ne_zero 2 (hne_sph v hv))
    · exact hcont_h.comp (continuousOn_id.inv₀ hne_sph) hmem_inv
  -- the two elementary integrals
  have h1 : circleIntegral (fun v : ℂ => 1 / v) 0 r⁻¹ = 2 * (Real.pi : ℂ) * Complex.I := by
    have hb := circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := (0 : ℂ)) (R := r⁻¹)
      (by rw [Metric.mem_ball, dist_zero_right]; simpa using hrinv0)
    simpa using hb
  have h2 : circleIntegral (fun v : ℂ => (v ^ 2)⁻¹ * (deriv g v⁻¹ / (g v⁻¹ - ζ))) 0 r⁻¹
      = circleIntegral (fun w : ℂ => deriv g w / (g w - ζ)) 0 r :=
    circleIntegral_comp_inv hr0 hcont_h
  have hval : circleIntegral (fun w : ℂ => deriv g w / (g w - ζ)) 0 r
      = 2 * (Real.pi : ℂ) * Complex.I := by
    have h := harg
    rw [hlog, circleIntegral.integral_sub hint1 hint2, h1, h2] at h
    exact (sub_eq_zero.mp h).symm
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  simp only [wind, hval]
  exact inv_mul_cancel₀ h2pi

end Work.Repel.Koebe
