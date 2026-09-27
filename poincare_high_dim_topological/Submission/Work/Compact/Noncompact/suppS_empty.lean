import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.mem_suppS_iff_of_expansion

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.Compact.Noncompact

noncomputable section

open scoped BigOperators

/-- A singular simplex has nonempty image: the standard simplex is nonempty. -/
lemma simplexSet_nonempty {X : TopCat} {k : ℕ} (σ : SimplexT X k) :
    (SimplexSet σ).Nonempty := by
  obtain ⟨z⟩ := (inferInstance : Nonempty (stdSimplex ℝ (Fin (k + 1))))
  exact ⟨_, Set.mem_range_self z⟩

/-- The submodule of `k`-chains supported in the empty set is trivial. -/
theorem suppS_empty {X : TopCat} (k : ℕ) :
    Work.Compact.Noncompact.suppS X (∅ : Set X) k = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro c hc
  rw [mem_suppS_iff_of_expansion] at hc
  obtain ⟨T, a, hc_eq, hsupp⟩ := hc
  rw [hc_eq]
  apply Finset.sum_eq_zero
  intro σ hσ
  have ha : a σ = 0 := by
    by_contra hne
    obtain ⟨x, hx⟩ := simplexSet_nonempty σ
    exact (hsupp σ hσ hne) hx
  rw [ha, zero_smul]

end

end Work.Compact.Noncompact
