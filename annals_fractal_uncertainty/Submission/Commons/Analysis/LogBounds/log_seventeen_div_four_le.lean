import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.LogBounds

theorem log_seventeen_div_four_le : Real.log ((17 : ℝ) / 4) ≤ 3 / 2 := by
  have hsum : (∑ i ∈ Finset.range 5, ((3 : ℝ) / 2) ^ i / (i.factorial : ℝ)) ≤ Real.exp (3 / 2) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 5
  have hval : (∑ i ∈ Finset.range 5, ((3 : ℝ) / 2) ^ i / (i.factorial : ℝ)) = 563 / 128 := by
    norm_num [Finset.sum_range_succ]
  have hlt : (17 : ℝ) / 4 ≤ Real.exp (3 / 2) := by
    rw [hval] at hsum
    linarith
  exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 17 / 4)).mpr hlt

end Commons.Analysis.LogBounds