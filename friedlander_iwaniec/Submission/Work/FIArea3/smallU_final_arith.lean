import Mathlib

namespace Work.FIArea3

/-- The closing arithmetic of the small-`u` crude pair-sum bound: for `w ≥ 3.7·10^7`,
`20 + (w+1)/233 + (3/2)(w+1)/log(w+1) + 10^5 ≤ w/12 + 1048575·log w`.
The difference is increasing on this range and equals `≈ 1.79·10^7` at `w = 3.7·10^7`; the same
conclusion follows by splitting at `w = 10^9` and using `log(w+1) ≥ 17.4` resp. `≥ 20.7`. -/
theorem smallU_final_arith (w : ℝ) (hw : (37000000 : ℝ) ≤ w) :
    (20 : ℝ) + (w + 1) / 233 + 3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5
      ≤ w / 12 + 1048575 * Real.log w := by
  -- We split at `2^28 = 268435456`, using `log(2^25) ≥ 17` and `log(2^28) ≥ 19` as lower bounds.
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog25 : (17 : ℝ) ≤ Real.log ((2 : ℝ) ^ 25) := by
    rw [Real.log_pow]; push_cast; nlinarith [hlog2]
  have hlog28 : (19 : ℝ) ≤ Real.log ((2 : ℝ) ^ 28) := by
    rw [Real.log_pow]; push_cast; nlinarith [hlog2]
  have hpow25 : ((2 : ℝ) ^ 25) ≤ 37000000 := by norm_num
  have hpow25pos : (0 : ℝ) < (2 : ℝ) ^ 25 := by norm_num
  have hpow28pos : (0 : ℝ) < (2 : ℝ) ^ 28 := by norm_num
  have hlogw17 : (17 : ℝ) ≤ Real.log w := by
    have h1 : ((2 : ℝ) ^ 25) ≤ w := le_trans hpow25 hw
    have h2 := Real.log_le_log hpow25pos h1
    linarith
  have hlogw1_17 : (17 : ℝ) ≤ Real.log (w + 1) := by
    have h1 : ((2 : ℝ) ^ 25) ≤ w + 1 := by linarith [le_trans hpow25 hw]
    have h2 := Real.log_le_log hpow25pos h1
    linarith
  by_cases hwle : w ≤ (2 : ℝ) ^ 28
  · -- Regime 1: `3.7·10^7 ≤ w ≤ 2^28`.  `log(w+1) ≥ 17`, so the log denominator is at least 17,
    -- and the resulting affine inequality in `w` is verified at the right endpoint `2^28`.
    have hbound : 3 / 2 * (w + 1) / Real.log (w + 1) ≤ 3 / 2 * (w + 1) / 17 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlogw1_17
    have hlin : (20 : ℝ) + (w + 1) / 233 + 3 / 2 * (w + 1) / 17 + 10 ^ 5
        ≤ w / 12 + 1048575 * 17 := by
      have hnum : (20 : ℝ) + (((2 : ℝ) ^ 28 + 1) / 233) + 3 / 2 * ((2 : ℝ) ^ 28 + 1) / 17
            + 10 ^ 5 ≤ (2 : ℝ) ^ 28 / 12 + 1048575 * 17 := by norm_num
      have hcoef : (0 : ℝ) < 1 / 233 + 3 / 34 - 1 / 12 := by norm_num
      have key : (1 / 233 + 3 / 34 - 1 / 12) * w ≤ (1 / 233 + 3 / 34 - 1 / 12) * (2 : ℝ) ^ 28 :=
        mul_le_mul_of_nonneg_left hwle (le_of_lt hcoef)
      nlinarith [hnum, key]
    have hrhs : w / 12 + 1048575 * 17 ≤ w / 12 + 1048575 * Real.log w := by
      have : 1048575 * (17 : ℝ) ≤ 1048575 * Real.log w :=
        mul_le_mul_of_nonneg_left hlogw17 (by norm_num)
      linarith
    calc (20 : ℝ) + (w + 1) / 233 + 3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5
        ≤ (20 : ℝ) + (w + 1) / 233 + 3 / 2 * (w + 1) / 17 + 10 ^ 5 := by linarith
      _ ≤ w / 12 + 1048575 * 17 := hlin
      _ ≤ w / 12 + 1048575 * Real.log w := hrhs
  · -- Regime 2: `w > 2^28`.  Now `log(w+1) ≥ 19`, and the affine inequality in `w` has a
    -- *negative* linear coefficient, so it holds for all `w ≥ 0`.
    have hwgt : ((2 : ℝ) ^ 28) < w := not_le.mp hwle
    have hlogw19 : (19 : ℝ) ≤ Real.log w := by
      have h1 : ((2 : ℝ) ^ 28) ≤ w := le_of_lt hwgt
      have h2 := Real.log_le_log hpow28pos h1
      linarith
    have hlogw1_19 : (19 : ℝ) ≤ Real.log (w + 1) := by
      have h1 : ((2 : ℝ) ^ 28) ≤ w + 1 := by linarith
      have h2 := Real.log_le_log hpow28pos h1
      linarith
    have hbound : 3 / 2 * (w + 1) / Real.log (w + 1) ≤ 3 / 2 * (w + 1) / 19 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlogw1_19
    have hlin : (20 : ℝ) + (w + 1) / 233 + 3 / 2 * (w + 1) / 19 + 10 ^ 5
        ≤ w / 12 + 1048575 * 19 := by
      have hcoef : (1 : ℝ) / 233 + 3 / 38 - 1 / 12 < 0 := by norm_num
      have hwpos : (0 : ℝ) ≤ w := by linarith
      have key : (1 / 233 + 3 / 38 - 1 / 12) * w ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt hcoef) hwpos
      have hconst : (1 : ℝ) / 233 + 3 / 38 + 20 + 10 ^ 5 - 1048575 * 19 < 0 := by norm_num
      nlinarith [key, hconst]
    have hrhs : w / 12 + 1048575 * 19 ≤ w / 12 + 1048575 * Real.log w := by
      have : 1048575 * (19 : ℝ) ≤ 1048575 * Real.log w :=
        mul_le_mul_of_nonneg_left hlogw19 (by norm_num)
      linarith
    calc (20 : ℝ) + (w + 1) / 233 + 3 / 2 * (w + 1) / Real.log (w + 1) + 10 ^ 5
        ≤ (20 : ℝ) + (w + 1) / 233 + 3 / 2 * (w + 1) / 19 + 10 ^ 5 := by linarith
      _ ≤ w / 12 + 1048575 * 19 := hlin
      _ ≤ w / 12 + 1048575 * Real.log w := hrhs

end Work.FIArea3
