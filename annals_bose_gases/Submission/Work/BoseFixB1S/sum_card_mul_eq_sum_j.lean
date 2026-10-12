import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Submission.Work.BoseFixB1S.BoxFlatAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open scoped BigOperators

/-- The cardinality of a finset of `Fin N`, as a real number, is the sum of the indicator of
membership. -/
theorem card_cast_eq_sum_ite_mem {N : ℕ} (s : Finset (Fin N)) :
    (s.card : ℝ) = ∑ j : Fin N, (if j ∈ s then (1 : ℝ) else 0) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp

/-- Double counting: `Σ_p |p.1| · F p` over the disjoint pairs equals the same total mass counted
by summing, for each `j`, over the pairs whose first component contains `j`. -/
theorem sum_card_mul_eq_sum_j {N : ℕ} (F : Finset (Fin N) × Finset (Fin N) → ℝ) :
    ∑ p ∈ Work.BoseFixB1S.disjPairs N, (p.1.card : ℝ) * F p
      = ∑ j : Fin N, ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          (if j ∈ p.1 then F p else 0) := by
  rw [← Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [card_cast_eq_sum_ite_mem (p.1), Finset.sum_mul]
  simp only [ite_mul, one_mul, zero_mul]

end Work.BoseFixB1S
