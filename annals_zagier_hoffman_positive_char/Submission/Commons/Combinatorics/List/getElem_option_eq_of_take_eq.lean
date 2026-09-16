import Mathlib

namespace Commons.Combinatorics.List

theorem getElem_option_eq_of_take_eq {α : Type*} {a b : List α} {k : ℕ} (h : a.take k = b.take k) : ∀ j, j < k → a[j]? = b[j]? := by
  intro j hj
  rw [← List.getElem?_take_of_lt (l := a) hj, h, List.getElem?_take_of_lt (l := b) hj]

end Commons.Combinatorics.List
