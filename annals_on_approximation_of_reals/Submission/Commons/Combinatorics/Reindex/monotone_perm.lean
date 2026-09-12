import Mathlib
import Submission.Commons.Combinatorics.Fin.exists_sorted_perm

noncomputable section

namespace Commons.Combinatorics.Reindex

/-- Any finite sequence of real numbers can be reindexed monotonically: there is a
permutation `σ` of `Fin n` such that the reordered sequence `f (σ i)` is nondecreasing
in `i` (with respect to the natural order on `Fin n`). -/
theorem monotone_perm {n : ℕ} (f : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i j : Fin n, i.val ≤ j.val → f (σ i) ≤ f (σ j) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨Equiv.refl (Fin 0), ?_⟩
    intro i
    exact Fin.elim0 i
  · obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact Commons.Combinatorics.Fin.exists_sorted_perm f

end Commons.Combinatorics.Reindex
