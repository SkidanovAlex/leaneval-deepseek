import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum.Ineq

namespace Commons.Analysis.Real

theorem one_sub_pow_ge_one_sub_mul (x : ℝ) (r : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (r : ℝ) * x ≤ (1 - x) ^ r := by
  have _hx0 : 0 ≤ x := hx0
  have hx2 : -2 ≤ -x := by
    exact neg_le_neg (hx1.trans (by norm_num : (1 : ℝ) ≤ 2))
  simpa [sub_eq_add_neg] using (one_add_mul_le_pow hx2 r)

end Commons.Analysis.Real