import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

theorem rpow_quarter_one_sub_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (1 - t) ^ ((1 : ℝ) / 4) ≤ 1 - t / 4 := by
  set u : ℝ := 1 - t with hu
  have hu0 : 0 ≤ u := by linarith
  set s : ℝ := u ^ ((1 : ℝ) / 4) with hs
  have hs4 : s ^ 4 = u := by
    rw [hs, ← Real.rpow_natCast (u ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hu0]
    norm_num
  have hid : (s - 1) ^ 2 * (s ^ 2 + 2 * s + 3) = s ^ 4 - 4 * s + 3 := by ring
  have hnn : 0 ≤ s ^ 2 + 2 * s + 3 := by nlinarith [sq_nonneg (s + 1)]
  have hnonneg : 0 ≤ u - 4 * s + 3 := by
    have h := mul_nonneg (sq_nonneg (s - 1)) hnn
    rw [hid, hs4] at h
    linarith
  linarith

end Commons.Analysis.Real