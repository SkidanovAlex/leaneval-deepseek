import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic

namespace Commons.Combinatorics.Fin

theorem exists_sorted_perm {N : ℕ} (g : Fin (N + 1) → ℝ) :
    ∃ σ : Equiv.Perm (Fin (N + 1)),
      ∀ ⦃i j : Fin (N + 1)⦄, i.val ≤ j.val → g (σ i) ≤ g (σ j) := by
  refine ⟨Tuple.sort g, ?_⟩
  intro i j hij
  exact Tuple.monotone_sort g hij

end Commons.Combinatorics.Fin