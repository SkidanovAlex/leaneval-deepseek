import Mathlib.Algebra.BigOperators.Fin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Finset BigOperators

namespace Commons.Algebra.BigOperators

/-- The sum over the ordered pairs of DISTINCT entries of `Fin (n+1)` can be reindexed as an
iterated sum in which the second index runs over `Fin n` embedded by `Fin.succAbove`. -/
theorem sum_pairSet_eq_succAbove {n : ℕ} {M : Type*} [AddCommMonoid M]
    (F : Fin (n + 1) → Fin (n + 1) → M) :
    (∑ q ∈ (Finset.univ.filter (fun q : Fin (n + 1) × Fin (n + 1) => q.1 ≠ q.2)), F q.1 q.2)
      = ∑ i : Fin (n + 1), ∑ j' : Fin n, F i (i.succAbove j') := by
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succAbove (fun j => if i ≠ j then F i j else 0) i]
  rw [if_neg (not_not.mpr rfl), zero_add]
  apply Finset.sum_congr rfl
  intro j' _
  rw [if_pos (Fin.succAbove_ne i j').symm]

end Commons.Algebra.BigOperators