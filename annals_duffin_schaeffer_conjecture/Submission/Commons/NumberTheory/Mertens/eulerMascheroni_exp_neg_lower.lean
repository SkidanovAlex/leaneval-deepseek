import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Submission.Commons.NumberTheory.Mertens.mertens_lower

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Commons.NumberTheory.Mertens

/-- Lower bound for `log (8/7)`, from `log (1+x) ≥ 2x/(x+2)`. -/
private lemma log_eight_sevenths_ge : (2 / 15 : ℝ) ≤ Real.log (8 / 7) := by
  have h := Real.le_log_one_add_of_nonneg (x := 1 / 7) (by norm_num)
  have e : (1 : ℝ) + 1 / 7 = 8 / 7 := by norm_num
  rw [e] at h
  convert h using 1
  norm_num

/-- Upper bound for `log 7`. -/
private lemma log_seven_le : Real.log 7 ≤ 3 * Real.log 2 - 2 / 15 := by
  have h : Real.log 7 = 3 * Real.log 2 - Real.log (8 / 7) := by
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      ring
    have hmul : Real.log 7 = Real.log 8 + Real.log (7 / 8) := by
      have := Real.log_mul (x := (8 : ℝ)) (y := 7 / 8) (by norm_num) (by norm_num)
      rwa [show (8 : ℝ) * (7 / 8) = 7 by norm_num] at this
    have hinv : Real.log (7 / 8) = -Real.log (8 / 7) := by
      rw [show (7 / 8 : ℝ) = (8 / 7)⁻¹ by norm_num, Real.log_inv]
    rw [hmul, h8, hinv]
    ring
  rw [h]
  linarith [log_eight_sevenths_ge]

/-- Lower bound for `log (25/14)`. -/
private lemma log_25_14_ge : (0.5796204347 : ℝ) ≤ Real.log (25 / 14) := by
  have hdiv : Real.log (25 / 14) = Real.log 25 - Real.log 14 :=
    Real.log_div (by norm_num) (by norm_num)
  have h25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]
    ring
  have h14 : Real.log 14 = Real.log 2 + Real.log 7 := by
    rw [show (14 : ℝ) = 2 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hdiv, h25, h14]
  linarith [Real.log_five_gt_d9, Real.log_two_lt_d9, log_seven_le]

theorem eulerMascheroni_exp_neg_lower : (0.56 : ℝ) ≤ Real.exp (-Real.eulerMascheroniConstant) := by
  have h1 : Real.eulerMascheroniConstant < (harmonic 256 : ℝ) - Real.log 256 := by
    have := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
    simpa [Real.eulerMascheroniSeq'] using this
  have hH : (harmonic 256 : ℝ) < 6.1244 := by norm_num
  have hlog256 : (5.5451774424 : ℝ) < Real.log 256 := by
    have h : Real.log 256 = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      ring
    rw [h]
    linarith [Real.log_two_gt_d9]
  have hγ : Real.eulerMascheroniConstant < Real.log (25 / 14) := by
    linarith [h1, hH, hlog256, log_25_14_ge]
  have h2 : -Real.log (25 / 14) < -Real.eulerMascheroniConstant := neg_lt_neg hγ
  have h3 : Real.exp (-Real.log (25 / 14)) ≤ Real.exp (-Real.eulerMascheroniConstant) :=
    Real.exp_le_exp.mpr h2.le
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 25 / 14)] at h3
  norm_num at h3 ⊢
  exact h3

end Commons.NumberTheory.Mertens