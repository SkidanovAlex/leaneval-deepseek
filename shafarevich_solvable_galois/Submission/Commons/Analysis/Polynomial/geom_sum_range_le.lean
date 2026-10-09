import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

lemma geom_sum_range_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) : ∑ i ∈ Finset.range n, x ^ i ≤ (n : ℝ) * x ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · calc ∑ i ∈ Finset.range n, x ^ i
        ≤ ∑ i ∈ Finset.range n, x ^ (n - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            apply pow_le_pow_right₀ hx
            have := Finset.mem_range.mp hi
            omega
      _ = (n : ℝ) * x ^ (n - 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Commons.Analysis.Polynomial