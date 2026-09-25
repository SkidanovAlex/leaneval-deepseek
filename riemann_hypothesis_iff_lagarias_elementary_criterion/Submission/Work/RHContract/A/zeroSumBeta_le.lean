import Mathlib
import Submission.Commons.Analysis.Real.eulerMascheroni_sub_log_four_pi_le_twentieth

namespace Work.RHContract.A

-- Numerical bound for the zero-sum constant β = 2 + Real.eulerMascheroniConstant − Real.log (4·Real.pi).
theorem zeroSumBeta_le : 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) ≤ 48/1000 := by
  have hγ := Commons.Analysis.Real.eulerMascheroniConstant_lt_log_thirteen_half
  have hlogmul : Real.log (26 * Real.pi) = Real.log (13/2) + Real.log (4 * Real.pi) := by
    rw [← Real.log_mul (by norm_num : (13/2:ℝ) ≠ 0) (by positivity : (4*Real.pi) ≠ 0)]
    congr 1; ring
  have hlog : (4402/1000 : ℝ) ≤ Real.log (26 * Real.pi) := by
    rw [Real.le_log_iff_exp_le (by positivity : (0:ℝ) < 26 * Real.pi)]
    have h4 : Real.exp 4 < 54.59816 := by
      have heq : Real.exp 4 = (Real.exp 1) ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [heq]
      calc (Real.exp 1) ^ 4 < (2.7182818286 : ℝ) ^ 4 := by
            gcongr
            exact Real.exp_one_lt_d9
        _ < 54.59816 := by norm_num
    have h25 : Real.exp (2 / 5 : ℝ) ≤ 1119 / 750 := by
      have h := Real.exp_bound' (x := (2 / 5 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by norm_num)
      refine h.trans (le_of_eq ?_)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    have h500 : Real.exp (1 / 500 : ℝ) ≤ 1.002003 := by
      have h := Real.exp_bound' (x := (1 / 500 : ℝ)) (by norm_num) (by norm_num) (n := 2) (by norm_num)
      refine h.trans (le_of_eq ?_)
      norm_num [Finset.sum_range_succ, Nat.factorial]
    have hsplit : (4402/1000 : ℝ) = 4 + 2/5 + 1/500 := by norm_num
    rw [hsplit, Real.exp_add, Real.exp_add]
    calc Real.exp 4 * Real.exp (2/5) * Real.exp (1/500)
        ≤ 54.59816 * (1119/750) * 1.002003 := by gcongr
      _ ≤ 81.68 := by norm_num
      _ ≤ 26 * Real.pi := by nlinarith [Real.pi_gt_d20]
  linarith [hγ, hlog, hlogmul]

end Work.RHContract.A
