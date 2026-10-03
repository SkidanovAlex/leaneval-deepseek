import Mathlib

namespace Work.PertCrux

/-- Auxiliary: `Real.log 4 ≤ 2`. -/
private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hpow : Real.log 4 = 2 * Real.log 2 := by
    conv_lhs => rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [Real.log_pow]; norm_num
  rw [hpow]; linarith

theorem lin_absorb {N : ℝ} (hN : 65 ≤ N) :
    100 * N * (2 + Real.log (4 * N)) ≤ 190 * N * (2 + Real.log (N + 1)) := by
  have hNpos : 0 < N := by linarith
  have hlog4 : Real.log 4 ≤ 2 := log_four_le_two
  -- `Real.log (N + 1) ≥ 1`, since `Real.exp 1 < 3 ≤ N + 1`.
  have hlogN1 : 1 ≤ Real.log (N + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < N + 1)]
    have : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have hlogN : Real.log N ≤ Real.log (N + 1) := Real.log_le_log hNpos (by linarith)
  have hlog4N : Real.log (4 * N) = Real.log 4 + Real.log N :=
    Real.log_mul (by norm_num) (by linarith)
  -- the core estimate `10 * (2 + log (4N)) ≤ 19 * (2 + log (N+1))`
  have key : 10 * (2 + Real.log (4 * N)) ≤ 19 * (2 + Real.log (N + 1)) := by
    rw [hlog4N]
    nlinarith [hlog4, hlogN, hlogN1]
  calc (100 : ℝ) * N * (2 + Real.log (4 * N))
      = (10 * N) * (10 * (2 + Real.log (4 * N))) := by ring
    _ ≤ (10 * N) * (19 * (2 + Real.log (N + 1))) := by
        apply mul_le_mul_of_nonneg_left key
        linarith
    _ = 190 * N * (2 + Real.log (N + 1)) := by ring

end Work.PertCrux
