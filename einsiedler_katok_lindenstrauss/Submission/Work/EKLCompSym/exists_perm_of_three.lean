import Mathlib

namespace Work.EKLCompSym

/-- Any three pairwise distinct elements of `Fin 3` can be arranged as the images
of `0, 1, 2` under some permutation of `Fin 3`. -/
theorem exists_perm_of_three {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all <;> decide

end Work.EKLCompSym
