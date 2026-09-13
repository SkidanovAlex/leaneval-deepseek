import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Commons.Algebra.BigOperators

theorem sum_finCongr_ite_four {M : Type*} [AddCommMonoid M] {n : ℕ} (h : n = 4)
    (g : Fin 4 → Fin 4 → M) :
    (∑ j : Fin n, ∑ i : Fin n,
        (if i < j then g (Fin.cast h i) (Fin.cast h j) else 0))
      = ∑ j : Fin 4, ∑ i : Fin 4, (if i < j then g i j else 0) := by
  subst h
  simp

end Commons.Algebra.BigOperators