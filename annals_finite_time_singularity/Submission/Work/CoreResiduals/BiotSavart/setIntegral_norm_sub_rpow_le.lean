import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.integral_ball_sub_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.norm_bsField_diff_bound
import Submission.Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_eq_lintegral_of_nonneg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Set
open scoped ENNReal

/-- **Translation invariance of the set Lebesgue integral over an open ball.**  Replacing the
centre of a ball by a translate and the integration variable by its difference from the centre
does not change the `lintegral`:
`∫⁻_{B(c,r)} F (y - c) = ∫⁻_{B(0,r)} F`. -/
lemma lintegral_ball_sub_eq (c : Work.LWP.R3) (r : ℝ) (F : Work.LWP.R3 → ℝ≥0∞) :
    ∫⁻ y in Metric.ball c r, F (y - c) = ∫⁻ z in Metric.ball (0 : Work.LWP.R3) r, F z := by
  classical
  have hs : MeasurableSet (Metric.ball c r) := Metric.isOpen_ball.measurableSet
  have hs0 : MeasurableSet (Metric.ball (0 : Work.LWP.R3) r) := Metric.isOpen_ball.measurableSet
  have hmem : ∀ y : Work.LWP.R3, y ∈ Metric.ball c r ↔ y - c ∈ Metric.ball (0 : Work.LWP.R3) r := by
    intro y
    rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm, sub_zero]
  rw [← lintegral_indicator hs (fun y => F (y - c))]
  have h1 : (fun y => (Metric.ball c r).indicator (fun y => F (y - c)) y)
      = fun y => (Metric.ball (0 : Work.LWP.R3) r).indicator F (y - c) := by
    funext y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Metric.ball c r
    · simp [hy, (hmem y).mp hy]
    · have hy' : y - c ∉ Metric.ball (0 : Work.LWP.R3) r := fun h => hy ((hmem y).mpr h)
      simp [hy, hy']
  rw [h1, lintegral_sub_right_eq_self
    (fun z => (Metric.ball (0 : Work.LWP.R3) r).indicator F z) c]
  rw [lintegral_indicator hs0 F]

/-- **The near-singular Riesz-kernel estimate over a ball.**  For `R > 0`, `α < 1` and any centre
`x ∈ ℝ³`,
`∫_{B(0,R)} ‖x - a‖^{-2-α} da ≤ 4π (‖x‖ + R + 1)^{1-α} / (1 - α)`.

The ball `B(0,R)` is contained in the ball `B(x, ‖x‖+R+1)`; the integrand is a radial power of
the distance to its own singularity, whose integral over a ball is computed by
`lintegral_ball_norm_rpow` (`∫_{B(0,ρ)} ‖z‖^s = 4π ρ^{s+3}/(s+3)` for `s > -3`), together with
translation invariance `lintegral_ball_sub_eq`.  The conversion between the Bochner integral and
the `lintegral` uses `setIntegral_eq_lintegral_of_nonneg`. -/
theorem setIntegral_norm_sub_rpow_le {R α : ℝ} (hR : 0 < R) (hα1 : α < 1) (x : Work.LWP.R3) :
    ∫ a in Metric.closedBall (0 : Work.LWP.R3) R, ‖x - a‖ ^ (-2 - α)
      ≤ 4 * Real.pi * (‖x‖ + R + 1) ^ (1 - α) / (1 - α) := by
  have hs : (-3:ℝ) < -2 - α := by linarith
  have hpos : (0:ℝ) < ‖x‖ + R + 1 := by linarith [norm_nonneg x, hR]
  have hnn : ∀ a : Work.LWP.R3, 0 ≤ ‖x - a‖ ^ (-2 - α) :=
    fun a => Real.rpow_nonneg (norm_nonneg _) _
  have hmeas : AEStronglyMeasurable (fun a : Work.LWP.R3 => ‖x - a‖ ^ (-2 - α)) volume :=
    (show Measurable (fun a : Work.LWP.R3 => ‖x - a‖ ^ (-2 - α)) by
      measurability).aestronglyMeasurable
  have hCnn : 0 ≤ 4 * Real.pi * (‖x‖ + R + 1) ^ (1 - α) / (1 - α) := by
    apply div_nonneg <;> [positivity; linarith]
  have hlin : ∫⁻ a in Metric.closedBall (0 : Work.LWP.R3) R, ENNReal.ofReal (‖x - a‖ ^ (-2 - α))
      ≤ ENNReal.ofReal (4 * Real.pi * (‖x‖ + R + 1) ^ (1 - α) / (1 - α)) := by
    have hsub : Metric.closedBall (0 : Work.LWP.R3) R ⊆ Metric.ball x (‖x‖ + R + 1) := by
      intro a ha
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at ha
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
        _ ≤ R + ‖x‖ := by linarith
        _ < ‖x‖ + R + 1 := by linarith
    calc ∫⁻ a in Metric.closedBall (0 : Work.LWP.R3) R, ENNReal.ofReal (‖x - a‖ ^ (-2 - α))
        ≤ ∫⁻ a in Metric.ball x (‖x‖ + R + 1), ENNReal.ofReal (‖x - a‖ ^ (-2 - α)) :=
          lintegral_mono_set hsub
      _ = ∫⁻ a in Metric.ball x (‖x‖ + R + 1), ENNReal.ofReal (‖a - x‖ ^ (-2 - α)) := by
          apply lintegral_congr; intro a; rw [norm_sub_rev]
      _ = ∫⁻ z in Metric.ball (0 : Work.LWP.R3) (‖x‖ + R + 1),
            ENNReal.ofReal (‖z‖ ^ (-2 - α)) :=
          lintegral_ball_sub_eq x (‖x‖ + R + 1) (fun z => ENNReal.ofReal (‖z‖ ^ (-2 - α)))
      _ = ENNReal.ofReal (4 * Real.pi * (‖x‖ + R + 1) ^ ((-2 - α) + 3) / ((-2 - α) + 3)) :=
          lintegral_ball_norm_rpow (-2 - α) hs (‖x‖ + R + 1) hpos
      _ = ENNReal.ofReal (4 * Real.pi * (‖x‖ + R + 1) ^ (1 - α) / (1 - α)) := by
          have h : (-2 : ℝ) - α + 3 = 1 - α := by ring
          rw [h]
  rw [setIntegral_eq_lintegral_of_nonneg Metric.isClosed_closedBall.measurableSet hmeas hnn]
  exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin)
    (le_of_eq (ENNReal.toReal_ofReal hCnn))

end Work.CoreResiduals.BiotSavart
