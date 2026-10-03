import Mathlib

namespace Work.FIArea4.Vflip.Vfd

theorem mcLog_bound {H : ℝ} (hH : 1 ≤ H) :
    (Real.log (2 + H) + 1) ^ 2 ≤ 4 * (Real.log (2 * H) + 1) ^ 2 := by
  have hlog2H : Real.log 2 ≤ Real.log (2 * H) := Real.log_le_log (by norm_num) (by linarith)
  have hlogH : Real.log (2 + H) ≤ Real.log (2 * H) + Real.log 2 := by
    have hle : 2 + H ≤ 2 * H * 2 := by linarith
    calc Real.log (2 + H) ≤ Real.log (2 * H * 2) := Real.log_le_log (by linarith) hle
      _ = Real.log (2 * H) + Real.log 2 := Real.log_mul (by linarith) (by norm_num)
  have ha : 0 ≤ Real.log (2 + H) + 1 := by
    have : 0 ≤ Real.log (2 + H) := Real.log_nonneg (by linarith)
    linarith
  have hmain : Real.log (2 + H) + 1 ≤ 2 * (Real.log (2 * H) + 1) := by linarith
  calc (Real.log (2 + H) + 1) ^ 2 ≤ (2 * (Real.log (2 * H) + 1)) ^ 2 :=
        pow_le_pow_left₀ ha hmain 2
    _ = 4 * (Real.log (2 * H) + 1) ^ 2 := by ring

end Work.FIArea4.Vflip.Vfd
