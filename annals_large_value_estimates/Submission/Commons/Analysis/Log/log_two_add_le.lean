import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.Analysis.Log

/-- For `0 ≤ X ≤ Y` and `1 ≤ Y`, we have `log (2 + X) ≤ log Y + 2`. -/
theorem log_two_add_le {X Y : ℝ} (hX : 0 ≤ X) (hY : 1 ≤ Y) (hXY : X ≤ Y) :
    Real.log (2 + X) ≤ Real.log Y + 2 := by
  -- `exp 2 ≥ 4 > 3`
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have hpos : 0 < Real.exp 1 := Real.exp_pos 1
    have hgt : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    have expand : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [expand]
    nlinarith
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY
  have harg : 0 < 2 + X := by linarith
  -- `2 + X ≤ exp 2 * Y`
  have hle : 2 + X ≤ Real.exp 2 * Y := by
    have hc : (2 : ℝ) ≤ Real.exp 2 - 1 := by linarith
    have h1 : (2 : ℝ) ≤ (Real.exp 2 - 1) * Y := by
      calc (2 : ℝ) = 2 * 1 := by norm_num
        _ ≤ (Real.exp 2 - 1) * Y := by gcongr
    nlinarith [hXY, h1]
  have hprod : 0 < Real.exp 2 * Y := mul_pos (Real.exp_pos 2) hYpos
  have hmain := Real.log_le_log harg hle
  rw [Real.log_mul (Real.exp_ne_zero 2) hYpos.ne', Real.log_exp] at hmain
  linarith

end Commons.Analysis.Log