import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum.Core
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori

/-- Summing a function on `ℤ` over the integer interval `{0, 1, …, n - 1}` (which is `∅`
when `n = 0`) agrees with summing `f` over `Finset.range n`, the natural number `k`
being identified with the integer `(k : ℤ)`. -/
theorem sum_Icc_zero_pred_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (n : ℕ) :
    ∑ i ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1), f i = ∑ k ∈ Finset.range n, f (k : ℤ) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  congr 1
  · norm_num
  · ext k
    simp

end Work.BoseFixB2.DvApriori
