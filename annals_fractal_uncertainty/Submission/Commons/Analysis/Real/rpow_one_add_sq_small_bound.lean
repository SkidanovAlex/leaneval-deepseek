import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

theorem rpow_one_add_sq_small_bound (b : ℕ) (t : ℝ) (hb : b ≤ 3) (ht0 : 0 ≤ t) (ht : t ≤ 2) :
    (1 + t ^ 2) ^ ((1 - (b : ℝ)) / 2) ≤ 4 := by
  -- `hb` is not needed for the bound; the estimate holds for every `b ≥ 0`.
  have _hb : (b : ℝ) ≤ 3 := by exact_mod_cast hb
  -- base is at least 1
  have hbase1 : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  -- exponent is at most 1/2
  have hble : ((1 - (b : ℝ)) / 2) ≤ (1 / 2 : ℝ) := by
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    linarith
  have hstep1 : (1 + t ^ 2) ^ ((1 - (b : ℝ)) / 2) ≤ (1 + t ^ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase1 hble
  -- t^2 ≤ 4
  have ht2 : t ^ 2 ≤ 4 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht)]
  have hbase16 : 1 + t ^ 2 ≤ 16 := by linarith
  have hstep2 : (1 + t ^ 2) ^ (1 / 2 : ℝ) ≤ (16 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hbase16 (by norm_num)
  have h16 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
    rw [← Real.sqrt_eq_rpow]
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith [hstep1, hstep2, h16]

end Commons.Analysis.Real