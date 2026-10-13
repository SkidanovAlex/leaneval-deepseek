import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs
import Submission.Work.LWP.BiotSavart.nearField_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory

/-- **The shifted inverse-square bound.**  For `h : ℝ³`,
`∫⁻_{B(0,2‖h‖)} ‖y+h‖⁻² ≤ 12π‖h‖`.

The singularity `y = -h` sits inside the ball of radius `2‖h‖`, so the estimate is the
borderline `(dim = 3)` case.  It is obtained by translating the centre: every
`y ∈ B(0, 2‖h‖)` satisfies `‖y + h‖ ≤ ‖y‖ + ‖h‖ < 3‖h‖`, i.e. `B(0,2‖h‖) ⊆ B(-h, 3‖h‖)`,
and the inverse-square weight is exactly integrable on a ball about its own singularity
(`Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_le`, `12π‖h‖ = 4π·(3‖h‖)`).

The exponent `-2` is the real power `Real.rpow`, converted to `(‖·‖^2)⁻¹` pointwise by
`inv_natPow_eq_rpow_neg`; the shift `y ↦ y + h` is undone with the translation-invariance
`Work.LWP.BiotSavart.lintegral_closedBall_sub_eq`. -/
theorem lintegral_ball_shift_inv_sq (h : Work.LWP.R3) :
    ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y + h‖ ^ (-2:ℝ))
      ≤ ENNReal.ofReal (12 * Real.pi * ‖h‖) := by
  -- Pointwise: `‖z‖ ^ (-2 : ℝ) = (‖z‖ ^ 2)⁻¹`.
  have hpt : ∀ z : Work.LWP.R3, ENNReal.ofReal (‖z‖ ^ (-2:ℝ))
      = ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹) := by
    intro z
    congr 1
    rw [show (-2 : ℝ) = -(((2 : ℕ)) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg z),
      Real.rpow_natCast]
  -- The ball `B(0, 2‖h‖)` is contained in the ball `B(-h, 3‖h‖)` around the singularity.
  have hsub : Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖) ⊆ Metric.closedBall (-h) (3 * ‖h‖) := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add]
    have h1 : ‖y + h‖ ≤ ‖y‖ + ‖h‖ := norm_add_le y h
    linarith
  calc ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y + h‖ ^ (-2:ℝ))
      = ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖),
          ENNReal.ofReal ((‖y + h‖ ^ (2 : ℕ))⁻¹) :=
        lintegral_congr (fun y => hpt (y + h))
    _ ≤ ∫⁻ y in Metric.closedBall (-h) (3 * ‖h‖), ENNReal.ofReal ((‖y + h‖ ^ (2 : ℕ))⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ y in Metric.closedBall (-h) (3 * ‖h‖),
          ENNReal.ofReal ((‖y - (-h)‖ ^ (2 : ℕ))⁻¹) := by
        apply lintegral_congr; intro y; rw [sub_neg_eq_add]
    _ = ∫⁻ z in Metric.closedBall (0 : Work.LWP.R3) (3 * ‖h‖),
          ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹) :=
        Work.LWP.BiotSavart.lintegral_closedBall_sub_eq (-h) (3 * ‖h‖)
          (fun z => ENNReal.ofReal ((‖z‖ ^ (2 : ℕ))⁻¹))
    _ ≤ ENNReal.ofReal (4 * Real.pi * (3 * ‖h‖)) :=
        Work.LWP.BiotSavart.inv_sq_lintegral_closedBall_le (3 * ‖h‖)
          (by positivity)
    _ = ENNReal.ofReal (12 * Real.pi * ‖h‖) := by congr 1; ring

end Work.CoreResiduals.BiotSavart
