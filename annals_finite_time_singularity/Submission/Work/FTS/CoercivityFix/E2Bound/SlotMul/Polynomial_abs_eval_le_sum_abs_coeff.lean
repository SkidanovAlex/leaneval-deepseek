import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Basic.Real.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

theorem Polynomial_abs_eval_le_sum_abs_coeff (P : Polynomial ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    |P.eval t| ≤ ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| := by
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_pow]
  refine le_trans (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg t) ht) (abs_nonneg _)) ?_
  rw [mul_one]

end Work.FTS.CoercivityFix.E2Bound.SlotMul
