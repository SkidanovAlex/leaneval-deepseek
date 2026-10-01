import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.Data.Finset

theorem sum_Icc_eq_sum_log2_blocks {M : Type*} [AddCommMonoid M] (a b : ℕ) (g : ℕ → M) :
    (∑ t ∈ Finset.Icc a b, g t)
      = ∑ j ∈ Finset.range (Nat.log2 b + 1),
          ∑ t ∈ (Finset.Icc a b).filter (fun t => Nat.log2 t = j), g t := by
  classical
  -- `Nat.log2` is monotone (`Nat.log_mono_right` after rewriting to `Nat.log 2`).
  have hmono : ∀ {m n : ℕ}, m ≤ n → Nat.log2 m ≤ Nat.log2 n := by
    intro m n h
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right h
  symm
  calc ∑ j ∈ Finset.range (Nat.log2 b + 1),
          ∑ t ∈ (Finset.Icc a b).filter (fun t => Nat.log2 t = j), g t
      = ∑ j ∈ Finset.range (Nat.log2 b + 1),
          ∑ t ∈ Finset.Icc a b, if Nat.log2 t = j then g t else 0 := by
        simp_rw [Finset.sum_filter]
    _ = ∑ t ∈ Finset.Icc a b,
          ∑ j ∈ Finset.range (Nat.log2 b + 1), if Nat.log2 t = j then g t else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ t ∈ Finset.Icc a b, g t := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.sum_ite_eq, if_pos]
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hmono (Finset.mem_Icc.mp ht).2))

end Commons.Data.Finset