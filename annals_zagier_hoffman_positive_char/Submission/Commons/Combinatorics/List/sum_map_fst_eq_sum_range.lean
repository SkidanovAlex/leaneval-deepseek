import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat

namespace Commons.Combinatorics.List

theorem sum_map_fst_eq_sum_range {α : Type*} (L : List (ℕ × α)) :
    (L.map Prod.fst).sum = ∑ i ∈ Finset.range L.length, ((L[i]?).map Prod.fst).getD 0 := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ih]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some]
    omega

end Commons.Combinatorics.List