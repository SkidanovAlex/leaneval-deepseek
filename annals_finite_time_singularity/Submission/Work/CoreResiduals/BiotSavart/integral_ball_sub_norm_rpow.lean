import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.LWP.Defs
import Submission.Work.CoreResiduals.BiotSavart.radial_rpow_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set

/-- Translation of the radial power integral to an arbitrary centre: for `s > -3` and `r > 0`,
`∫_{B(x,r)} ‖a - x‖^s da = 4π r^{s+3}/(s+3)`.  This is the centred version
`radial_rpow_integral` together with translation invariance of Lebesgue measure. -/
theorem integral_ball_sub_norm_rpow (x : Work.LWP.R3) (r s : ℝ) (hs : -3 < s) (hr : 0 < r) :
    ∫ a in Metric.ball x r, (‖a - x‖ : ℝ) ^ s = 4 * Real.pi * r ^ (s + 3) / (s + 3) := by
  have hshift : ∫ a in Metric.ball x r, (‖a - x‖ : ℝ) ^ s
      = ∫ z in Metric.ball (0 : Work.LWP.R3) r, (‖z‖ : ℝ) ^ s := by
    calc ∫ a in Metric.ball x r, (‖a - x‖ : ℝ) ^ s
        = ∫ a, (Metric.ball x r).indicator (fun a => (‖a - x‖ : ℝ) ^ s) a :=
          (integral_indicator measurableSet_ball).symm
      _ = ∫ z, (Metric.ball x r).indicator (fun a => (‖a - x‖ : ℝ) ^ s) (z + x) :=
          (integral_add_right_eq_self
            (fun a => (Metric.ball x r).indicator (fun a => (‖a - x‖ : ℝ) ^ s) a) x).symm
      _ = ∫ z, (Metric.ball (0 : Work.LWP.R3) r).indicator (fun a => (‖a‖ : ℝ) ^ s) z := by
          apply integral_congr_ae
          filter_upwards with z
          by_cases hz : z ∈ Metric.ball (0 : Work.LWP.R3) r
          · have hz' : ‖z‖ < r := by rwa [Metric.mem_ball, dist_zero_right] at hz
            have hzx : z + x ∈ Metric.ball x r := by
              rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
              exact hz'
            rw [Set.indicator_of_mem hzx, Set.indicator_of_mem hz, add_sub_cancel_right]
          · have hz' : r ≤ ‖z‖ := by
              rw [Metric.mem_ball, dist_zero_right] at hz
              exact not_lt.mp hz
            have hzx : z + x ∉ Metric.ball x r := by
              rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
              exact not_lt.mpr hz'
            rw [Set.indicator_of_notMem hzx, Set.indicator_of_notMem hz]
      _ = ∫ z in Metric.ball (0 : Work.LWP.R3) r, (‖z‖ : ℝ) ^ s :=
          integral_indicator measurableSet_ball
  rw [hshift]
  exact radial_rpow_integral s hs r hr

end Work.CoreResiduals.BiotSavart
