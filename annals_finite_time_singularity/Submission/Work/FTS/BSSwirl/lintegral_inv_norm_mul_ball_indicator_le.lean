import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow
import Submission.Work.CoreResiduals.BiotSavart.setIntegral_norm_sub_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Riesz-kernel `lintegral` over a ball, in indicator form

For `x ∈ ℝ³`, `r ≥ 0` and `‖x‖ ≤ A`,

`∫⁻ y, ‖x - y‖⁻¹ · 1_{B(0,r)}(y) ≤ 2π (r + A + 1)²`.

This is the `lintegral` (indicator) form of `setIntegral_norm_sub_rpow_le` at the exponent
`-1 = -2 - α` with `α = -1 < 1`: the ball `B(0,r)` is contained in `B(x, ‖x‖ + r + 1)`, the
integrand is a radial power of the distance to its own singularity, and
`∫⁻_{B(0,ρ)} ‖z‖^{-1} = ofReal (4π ρ²/2) = ofReal (2π ρ²)` by `lintegral_ball_norm_rpow`
(with `s = -1`, so `s + 3 = 2`) and translation invariance `lintegral_ball_sub_eq`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Work.FTS.BSSwirl

theorem lintegral_inv_norm_mul_ball_indicator_le (x : Work.FTS.BSSwirl.R3) {r A : ℝ}
    (hr : 0 ≤ r) (hx : ‖x‖ ≤ A) :
    ∫⁻ y : Work.FTS.BSSwirl.R3, ENNReal.ofReal ((‖x - y‖)⁻¹) *
        ENNReal.ofReal
          ((Metric.closedBall (0 : Work.FTS.BSSwirl.R3) r).indicator (fun _ => (1 : ℝ)) y)
      ≤ ENNReal.ofReal (2 * Real.pi * (r + A + 1) ^ 2) := by
  classical
  -- The product with the `ℝ`-valued indicator is the `ℝ≥0∞`-valued indicator of the ball.
  have hcongr : (fun y : R3 => ENNReal.ofReal ((‖x - y‖)⁻¹) *
        ENNReal.ofReal ((Metric.closedBall (0 : R3) r).indicator (fun _ => (1 : ℝ)) y))
      = fun y : R3 => (Metric.closedBall (0 : R3) r).indicator
          (fun y => ENNReal.ofReal ((‖x - y‖)⁻¹)) y := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0 : R3) r
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      simp
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      simp
  rw [hcongr, lintegral_indicator Metric.isClosed_closedBall.measurableSet
    (fun y => ENNReal.ofReal ((‖x - y‖)⁻¹))]
  set ρ : ℝ := ‖x‖ + r + 1 with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith [norm_nonneg x, hr]
  have hρpos : 0 < ρ := by rw [hρ]; linarith [norm_nonneg x, hr]
  -- The ball `B(0,r)` sits inside `B(x,ρ)`.
  have hsub : Metric.closedBall (0 : R3) r ⊆ Metric.ball x ρ := by
    intro a ha
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at ha
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖a - x‖ ≤ ‖a‖ + ‖x‖ := norm_sub_le a x
    calc ‖a - x‖ ≤ ‖a‖ + ‖x‖ := h1
      _ ≤ r + ‖x‖ := by linarith
      _ < ρ := by rw [hρ]; linarith
  have hchain : ∫⁻ y in Metric.closedBall (0 : R3) r, ENNReal.ofReal ((‖x - y‖)⁻¹)
      ≤ ENNReal.ofReal (2 * Real.pi * (r + A + 1) ^ 2) := by
    calc ∫⁻ y in Metric.closedBall (0 : R3) r, ENNReal.ofReal ((‖x - y‖)⁻¹)
        ≤ ∫⁻ y in Metric.ball x ρ, ENNReal.ofReal ((‖x - y‖)⁻¹) := lintegral_mono_set hsub
      _ = ∫⁻ y in Metric.ball x ρ, ENNReal.ofReal (‖x - y‖ ^ (-1:ℝ)) := by
            apply lintegral_congr; intro y; rw [Real.rpow_neg_one]
      _ = ∫⁻ y in Metric.ball x ρ, ENNReal.ofReal (‖y - x‖ ^ (-1:ℝ)) := by
            apply lintegral_congr; intro y; rw [norm_sub_rev]
      _ = ∫⁻ z in Metric.ball (0 : R3) ρ, ENNReal.ofReal (‖z‖ ^ (-1:ℝ)) :=
            Work.CoreResiduals.BiotSavart.lintegral_ball_sub_eq x ρ
              (fun z => ENNReal.ofReal (‖z‖ ^ (-1:ℝ)))
      _ = ENNReal.ofReal (4 * Real.pi * ρ ^ ((-1:ℝ) + 3) / ((-1:ℝ) + 3)) :=
            Work.CoreResiduals.BiotSavart.lintegral_ball_norm_rpow (-1) (by norm_num) ρ hρpos
      _ = ENNReal.ofReal (2 * Real.pi * ρ ^ 2) := by
            congr 1
            rw [show ((-1:ℝ) + 3) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            ring
      _ ≤ ENNReal.ofReal (2 * Real.pi * (r + A + 1) ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            have hρle : ρ ≤ r + A + 1 := by rw [hρ]; linarith
            have hsq : ρ ^ 2 ≤ (r + A + 1) ^ 2 := pow_le_pow_left₀ hρ0 hρle 2
            nlinarith [Real.pi_pos, hsq]
  exact hchain

end Work.FTS.BSSwirl
