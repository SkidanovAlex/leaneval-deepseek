import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Regime

open Work.BoseBox

open Work.BoseFixB1

theorem one_le_mu_d_mul_sideAt_cube {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht : μ * A ^ 3 ≤ 1) : 1 ≤ μ * ((paramsAt μ A).d * sideAt μ A) ^ 3 := by
  rw [mu_d_mul_sideAt_cube_eq hA hμ]
  exact one_le_fsXp_of (by positivity) ht (by norm_num)

end Work.BoseFixB1.Regime
