import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Nat

namespace Commons.Algebra.BigOperators

open scoped BigOperators

theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m n : ℕ) :
    ∑ i ∈ Finset.range (m * n), f i
      = ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, f (a + m * b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [Nat.add_comm]

end Commons.Algebra.BigOperators