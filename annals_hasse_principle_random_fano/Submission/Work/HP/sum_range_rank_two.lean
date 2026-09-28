import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP

theorem sum_range_rank_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (X : ℝ) (hrk : rk L = 2) :
    (∑ i ∈ Finset.range (rk L + 1),
        X ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1))
      = X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1 := by
  rw [hrk]
  simp only [Finset.sum_range_succ, Finset.prod_range_succ, Finset.prod_range_zero,
    Finset.sum_range_zero]
  norm_num [Finset.prod_range_zero, Finset.sum_range_zero]

end Work.HP
