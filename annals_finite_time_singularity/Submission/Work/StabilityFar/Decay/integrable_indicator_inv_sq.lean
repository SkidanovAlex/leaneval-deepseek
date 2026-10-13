import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.StabilityFar.Defs
import Submission.Work.LWP.BiotSavart.nearField_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.StabilityFar.Decay

open MeasureTheory

/-- The singular weight `‖x-y‖⁻²` has finite integral over the closed ball `B(0,R)`, with the
explicit bound `4π(‖x‖+R)`: enlarge `B(0,R)` to the ball `B(x, ‖x‖+R)` centred at `x`, which
contains it (because `‖y‖ ≤ R` gives `‖y-x‖ ≤ R + ‖x‖`), and apply the radial computation
`∫_{B(x,r)}‖y-x‖⁻² = 4πr` of `Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_shifted_le`. -/
lemma lintegral_inv_sq_closedBall_le {R : ℝ} (hR : 0 ≤ R) (x : R3) :
    ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ENNReal.ofReal (4 * Real.pi * (‖x‖ + R)) := by
  have hsub : Metric.closedBall (0 : R3) R ⊆ Metric.closedBall x (‖x‖ + R) := by
    intro y hy
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
    simp only [Metric.mem_closedBall, dist_eq_norm]
    calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := by linarith
      _ = ‖x‖ + R := by ring
  calc ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹)
      ≤ ∫⁻ y in Metric.closedBall x (‖x‖ + R), ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ y in Metric.closedBall x (‖x‖ + R), ENNReal.ofReal ((‖y - x‖ ^ (2 : ℕ))⁻¹) := by
        apply lintegral_congr
        intro y
        rw [norm_sub_rev]
    _ ≤ ENNReal.ofReal (4 * Real.pi * (‖x‖ + R)) :=
        Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_shifted_le x (by positivity)

theorem integrable_indicator_inv_sq (x : Work.StabilityFar.R3) {R C : ℝ} (hC : 0 ≤ C) :
    MeasureTheory.Integrable (fun y : Work.StabilityFar.R3 =>
      (Metric.closedBall (0 : Work.StabilityFar.R3) R).indicator
        (fun y => C * ((‖x - y‖ ^ (2 : ℕ))⁻¹)) y) MeasureTheory.volume := by
  classical
  rcases lt_or_ge R 0 with hR | hR
  · have hempty : Metric.closedBall (0 : R3) R = ∅ := Metric.closedBall_eq_empty.mpr hR
    rw [hempty, Set.indicator_empty']
    exact integrable_zero R3 ℝ MeasureTheory.volume
  rw [MeasureTheory.integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
  rw [MeasureTheory.IntegrableOn]
  refine ⟨?_, ?_⟩
  · apply Measurable.aestronglyMeasurable
    measurability
  · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have hbound := lintegral_inv_sq_closedBall_le (R := R) hR x
    calc ∫⁻ y in Metric.closedBall (0 : R3) R,
            ENNReal.ofReal ‖C * ((‖x - y‖ ^ (2 : ℕ))⁻¹)‖
        = ∫⁻ y in Metric.closedBall (0 : R3) R,
            ENNReal.ofReal C * ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) := by
          apply lintegral_congr
          intro y
          rw [Real.norm_of_nonneg (mul_nonneg hC (by positivity)), ENNReal.ofReal_mul hC]
      _ = ENNReal.ofReal C *
            ∫⁻ y in Metric.closedBall (0 : R3) R, ENNReal.ofReal ((‖x - y‖ ^ (2 : ℕ))⁻¹) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (4 * Real.pi * (‖x‖ + R)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end Work.StabilityFar.Decay
