import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

namespace Commons.Combinatorics.List

theorem take_eq_take_iff_getElem_option {α : Type*} (a b : List α) (k : ℕ) :
    a.take k = b.take k ↔ ∀ j, j < k → a[j]? = b[j]? := by
  constructor
  · intro h j hj
    calc a[j]? = (a.take k)[j]? := (List.getElem?_take_of_lt (l := a) hj).symm
      _ = (b.take k)[j]? := by rw [h]
      _ = b[j]? := List.getElem?_take_of_lt (l := b) hj
  · intro h
    apply List.ext_getElem?
    intro n
    by_cases hn : n < k
    · simp [hn, h n hn]
    · simp [hn]

end Commons.Combinatorics.List