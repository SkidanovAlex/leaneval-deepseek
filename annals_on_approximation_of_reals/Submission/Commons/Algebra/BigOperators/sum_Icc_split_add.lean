import Mathlib.Algebra.BigOperators.Intervals

namespace Commons.Algebra.BigOperators

open scoped BigOperators
open Finset

/-- Split a finite sum over an integer interval `Icc a c` into the part `Icc a b` and the part
`Icc (b+1) c`, for `a ≤ b ≤ c`. -/
theorem sum_Icc_split_add {α : Type*} [AddCommMonoid α] (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c)
    (f : ℕ → α) : (∑ i ∈ Finset.Icc a c, f i) = (∑ i ∈ Finset.Icc a b, f i) + (∑ i ∈ Finset.Icc (b+1) c, f i) := by
  rw [← Finset.Ico_add_one_right_eq_Icc a c, ← Finset.Ico_add_one_right_eq_Icc a b,
    ← Finset.Ico_add_one_right_eq_Icc (b + 1) c]
  exact (Finset.sum_Ico_consecutive f (le_trans hab (Nat.le_succ b)) (Nat.succ_le_succ hbc)).symm

end Commons.Algebra.BigOperators