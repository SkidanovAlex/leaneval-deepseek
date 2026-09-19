import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.Data.Finset

/-- Shifting the argument of a sum over an integer interval: summing `f (n + h)`
over `n ∈ Icc a b` equals summing `f m` over `m ∈ Icc (a + h) (b + h)`. -/
theorem sum_Icc_comp_add {M : Type*} [AddCommMonoid M] (a b h : ℕ) (f : ℕ → M) :
    (∑ n ∈ Finset.Icc a b, f (n + h)) = ∑ m ∈ Finset.Icc (a + h) (b + h), f m := by
  rw [← Finset.map_add_right_Icc (a := a) (b := b) (c := h), Finset.sum_map]
  simp

end Commons.Data.Finset