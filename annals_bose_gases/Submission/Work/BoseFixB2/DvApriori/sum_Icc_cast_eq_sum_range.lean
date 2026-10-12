import Mathlib.Computability.Reduce
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori

theorem sum_Icc_cast_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (m n : ℕ) :
    ∑ i ∈ Finset.Icc (m : ℤ) (n : ℤ), f i
      = ∑ k ∈ Finset.range (n + 1 - m), f ((k : ℤ) + (m : ℤ)) := by
  -- `Int.Icc_eq_finset_map` writes `Icc a b` as the image of `range (b + 1 - a).toNat`
  -- under `j ↦ a + j`.  Here `a = (m : ℤ)`, `b = (n : ℤ)`, so the range length is
  -- `((n : ℤ) + 1 - (m : ℤ)).toNat`, which is `n + 1 - m` (truncated subtraction on `ℕ`
  -- agrees with the `ℤ`-`toNat` of the difference because `(n + 1 : ℕ) - m` truncates the
  -- same way).  The remaining discrepancy is only the order of the two summands.
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  have h : ((n : ℤ) + 1 - (m : ℤ)).toNat = n + 1 - m := by
    have : ((n : ℤ) + 1 - (m : ℤ)) = ((n + 1 : ℕ) : ℤ) - ((m : ℕ) : ℤ) := by
      push_cast; ring
    rw [this, Int.toNat_sub]
  rw [h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  show f ((m : ℤ) + (k : ℤ)) = f ((k : ℤ) + (m : ℤ))
  rw [add_comm]

end Work.BoseFixB2.DvApriori
