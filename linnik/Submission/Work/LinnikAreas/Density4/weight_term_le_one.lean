import Mathlib

namespace Work.LinnikAreas.Density4

lemma weight_term_le_one (A : ℝ) (hA : 2 ≤ A) (m : ℕ) :
    (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) ≤ 1 := by
  have hp : (1:ℝ) ≤ (2:ℝ)^m := one_le_pow₀ (by norm_num)
  have h3 : (3:ℝ) ≤ 2 + (2:ℝ)^m := by linarith
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
    exact Real.exp_one_lt_three
  have hlog : 1 ≤ Real.log (2 + (2:ℝ)^m) :=
    le_trans hlog3.le (Real.log_le_log (by norm_num) h3)
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith)

end Work.LinnikAreas.Density4
