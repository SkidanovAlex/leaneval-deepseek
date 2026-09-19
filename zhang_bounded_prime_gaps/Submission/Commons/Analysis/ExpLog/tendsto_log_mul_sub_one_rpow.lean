import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Submission.Commons.Analysis.ExpLog.tendsto_integral_log_exp_neg_Ioi

namespace Commons.Analysis.ExpLog

private lemma log_mul_sub_one_rpow_nonneg {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ 1 - (3 : ℝ) ^ (-ε) := by
  have hb_le : (3 : ℝ) ^ (-ε) ≤ (3 : ℝ) ^ (0 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  have hb1 : (3 : ℝ) ^ (-ε) ≤ 1 := by simpa using hb_le
  linarith

private lemma log_mul_sub_one_rpow_upper (ε : ℝ) :
    1 - (3 : ℝ) ^ (-ε) ≤ Real.log 3 * ε := by
  have hb : 0 < (3 : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (-ε)
  have hle : (-ε) * Real.log 3 ≤ (3 : ℝ) ^ (-ε) - 1 := by
    simpa [Real.log_rpow (by norm_num : (0 : ℝ) < 3) (-ε)] using
      (Real.log_le_sub_one_of_pos hb)
  nlinarith

lemma tendsto_log_mul_sub_one_rpow :
    Filter.Tendsto (fun ε : ℝ => Real.log ε * (1 - (3 : ℝ) ^ (-ε)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
  have hIoc : Set.Ioc (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact ⟨hx.1, le_of_lt hx.2⟩
  have hlg : Filter.Tendsto (fun ε : ℝ => Real.log ε * ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
    simpa [Real.rpow_one] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) (by norm_num : (0 : ℝ) < 1))
  have hLlim : Filter.Tendsto (fun ε : ℝ => Real.log 3 * (ε * Real.log ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
    simpa [mul_comm] using hlg.const_mul (Real.log 3)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun ε : ℝ => Real.log 3 * (ε * Real.log ε))
    (h := fun _ : ℝ => (0 : ℝ))
    (a := (0 : ℝ))
  · simpa using hLlim
  · exact tendsto_const_nhds
  · filter_upwards [hIoc] with ε hε
    have hε0 : 0 < ε := hε.1
    have hε1 : ε ≤ 1 := hε.2
    have hle : 1 - (3 : ℝ) ^ (-ε) ≤ Real.log 3 * ε := log_mul_sub_one_rpow_upper ε
    have hlogle : Real.log ε ≤ 0 := Real.log_nonpos (le_of_lt hε0) hε1
    have hmul : Real.log ε * (Real.log 3 * ε) ≤
        Real.log ε * (1 - (3 : ℝ) ^ (-ε)) := by
      exact mul_le_mul_of_nonpos_left hle hlogle
    calc
      Real.log 3 * (ε * Real.log ε) = Real.log ε * (Real.log 3 * ε) := by ring
      _ ≤ Real.log ε * (1 - (3 : ℝ) ^ (-ε)) := hmul
  · filter_upwards [hIoc] with ε hε
    have hε0 : 0 < ε := hε.1
    have hε1 : ε ≤ 1 := hε.2
    have hlogle : Real.log ε ≤ 0 := Real.log_nonpos (le_of_lt hε0) hε1
    have hge0 : 0 ≤ 1 - (3 : ℝ) ^ (-ε) := log_mul_sub_one_rpow_nonneg (le_of_lt hε0)
    exact mul_nonpos_of_nonpos_of_nonneg hlogle hge0

end Commons.Analysis.ExpLog