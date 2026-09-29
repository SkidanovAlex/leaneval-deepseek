import Mathlib

namespace Work.AAsm

/-- `exp (127/25) < 161`, obtained from `exp 5 = (exp 1)^5`, the decimal bound
`exp 1 < 2.7182818286`, and a Taylor upper bound for `exp (2/25)`. -/
private lemma exp_127_25_lt_161 : Real.exp (127 / 25) < 161 := by
  have hsplit : (127 : ℝ) / 25 = 5 + 2 / 25 := by norm_num
  rw [hsplit, Real.exp_add]
  have h5 : Real.exp 5 < (2.7182818286 : ℝ) ^ 5 := by
    have he : Real.exp 5 = Real.exp (1 : ℝ) ^ 5 := by simp [← Real.exp_nat_mul]
    rw [he]
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (by positivity) (by norm_num)
  have h2 : Real.exp (2 / 25) < 1.0833138 := by
    have hb := Real.exp_bound' (show (0 : ℝ) ≤ 2 / 25 by norm_num)
      (show (2 : ℝ) / 25 ≤ 1 by norm_num) (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb
    linarith [hb]
  nlinarith [h5, h2, Real.exp_pos 5, Real.exp_pos (2 / 25)]

theorem a_log_bounds :
    Real.log (256 * ((2383521894760738000000000 : ℝ) / 3774888615849058882987209)) > 127 / 25 ∧
    Real.log 5660 < 173 / 20 ∧
    Real.log ((500 : ℝ) / 283) < 29 / 50 := by
  refine ⟨?_, ?_, ?_⟩
  · change (127 : ℝ) / 25 <
      Real.log (256 * ((2383521894760738000000000 : ℝ) / 3774888615849058882987209))
    rw [Real.lt_log_iff_exp_lt (show (0 : ℝ) <
      256 * ((2383521894760738000000000 : ℝ) / 3774888615849058882987209) by norm_num)]
    calc Real.exp (127 / 25) < 161 := exp_127_25_lt_161
      _ < 256 * ((2383521894760738000000000 : ℝ) / 3774888615849058882987209) := by norm_num
  · rw [Real.log_lt_iff_lt_exp (show (0 : ℝ) < 5660 by norm_num)]
    exact lt_of_lt_of_le
      (by norm_num : (5660 : ℝ) < ∑ i ∈ Finset.range 17, ((173 : ℝ) / 20) ^ i / (↑i.factorial : ℝ))
      (Real.sum_le_exp_of_nonneg (by norm_num) 17)
  · rw [Real.log_lt_iff_lt_exp (show (0 : ℝ) < (500 : ℝ) / 283 by norm_num)]
    exact lt_of_lt_of_le
      (by norm_num : (500 : ℝ) / 283 < ∑ i ∈ Finset.range 4, ((29 : ℝ) / 50) ^ i / (↑i.factorial : ℝ))
      (Real.sum_le_exp_of_nonneg (by norm_num) 4)

end Work.AAsm
