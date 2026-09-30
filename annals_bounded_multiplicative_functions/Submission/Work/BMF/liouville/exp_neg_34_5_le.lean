import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Nat

/-- Auxiliary: the 11-term Taylor partial sum of `exp (34/5)` exceeds `800`. -/
private lemma taylor_34_5_ge : (800 : ℝ) ≤ ∑ i ∈ Finset.range 11, (34/5 : ℝ) ^ i / (i ! : ℝ) := by
  norm_num [Finset.sum_range_succ]

theorem exp_neg_34_5_le : Real.exp (-(34/5)) ≤ 1/800 := by
  have h2 : (800 : ℝ) ≤ Real.exp (34/5) :=
    le_trans taylor_34_5_ge (Real.sum_le_exp_of_nonneg (by norm_num) 11)
  have h3 : 1 / Real.exp (34/5) ≤ 1 / (800 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) h2
  rw [Real.exp_neg, one_div]
  simpa using h3

end Work.BMF.liouville
