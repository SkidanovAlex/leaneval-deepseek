import Mathlib
import Submission.Work.HP.ceil_logb_bounds

/-!
# `ceil_logb_rpow_le`

For every real `x ≥ 1`, with `n = ⌈logb 2 x⌉₊` the ceiling of the binary logarithm of `x`,

`2 ^ (71 * n / 3) ≤ 2 ^ (71 / 3) * x ^ (71 / 3)`.

Indeed, `Work.HP.ceil_logb_bounds` gives `2 ^ ⌈logb 2 x⌉₊ ≤ 2 * x`, and raising this
inequality to the positive power `71/3` (via monotonicity of `ℝ`-powers) multiplies the
gain `2 ^ (71/3)` into the right-hand side.
-/

namespace Work.HP.MDEstimates

theorem ceil_logb_rpow_le (x : ℝ) (hx : 1 ≤ x) :
    (2:ℝ) ^ (71 * (⌈Real.logb 2 x⌉₊ : ℝ) / 3) ≤ 2 ^ ((71:ℝ)/3) * x ^ ((71:ℝ)/3) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  obtain ⟨-, h2n⟩ := Work.HP.ceil_logb_bounds hx
  rw [← Real.rpow_natCast 2 ⌈Real.logb 2 x⌉₊] at h2n
  have hstep :
      ((2:ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ)) ^ ((71:ℝ)/3) ≤ (2 * x) ^ ((71:ℝ)/3) :=
    Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h2n (by norm_num)
  have hpow : (2:ℝ) ^ (71 * (⌈Real.logb 2 x⌉₊ : ℝ) / 3)
      = ((2:ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ)) ^ ((71:ℝ)/3) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  calc (2:ℝ) ^ (71 * (⌈Real.logb 2 x⌉₊ : ℝ) / 3)
      = ((2:ℝ) ^ (⌈Real.logb 2 x⌉₊ : ℝ)) ^ ((71:ℝ)/3) := hpow
      _ ≤ (2 * x) ^ ((71:ℝ)/3) := hstep
      _ = 2 ^ ((71:ℝ)/3) * x ^ ((71:ℝ)/3) := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hx0)]

end Work.HP.MDEstimates
