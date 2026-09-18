import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace Commons.NumberTheory.DuffinSchaeffer

/-- On the unit additive circle, an open ball of radius `δ` has volume at most `2δ`
(the Haar measure on `UnitAddCircle` is normalised to have total mass `1`). -/
theorem volume_ball_le_ofReal_two_mul (x : UnitAddCircle) {δ : ℝ} (hδ : 0 ≤ δ) :
    MeasureTheory.volume (Metric.ball x δ) ≤ ENNReal.ofReal (2 * δ) := by
  calc
    MeasureTheory.volume (Metric.ball x δ)
        ≤ MeasureTheory.volume (Metric.closedBall x δ) := measure_mono ball_subset_closedBall
    _ = ENNReal.ofReal (min (1 : ℝ) (2 * δ)) := by
        exact AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) δ
    _ ≤ ENNReal.ofReal (2 * δ) := ENNReal.ofReal_le_ofReal (min_le_right (1 : ℝ) (2 * δ))

end Commons.NumberTheory.DuffinSchaeffer