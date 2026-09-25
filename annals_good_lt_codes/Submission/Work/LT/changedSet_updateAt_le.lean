import Mathlib
import Submission.Work.LT.local_search_defs

namespace Work.LT

lemma changedSet_updateAt_le {G : Type} [Fintype G] {Δ : ℕ}
    (W W0 : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (α β : Fin 2) (g : G)
    (w : Fin Δ × Fin Δ → ZMod 2) :
    (Work.LT.changedSet (Work.LT.updateAt W α β g w) W0).card ≤
      (Work.LT.changedSet W W0).card + 1 := by
  classical
  have hsub : changedSet (updateAt W α β g w) W0 ⊆ insert (α, β, g) (changedSet W W0) := by
    intro v hv
    by_cases h : v = (α, β, g)
    · rw [Finset.mem_insert]
      exact Or.inl h
    · rw [Finset.mem_insert]
      refine Or.inr ?_
      simp only [changedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      have hne : ¬(v.1 = α ∧ v.2.1 = β ∧ v.2.2 = g) := by
        rintro ⟨h1, h2, h3⟩
        exact h (Prod.ext h1 (Prod.ext h2 h3))
      rw [updateAt_of_ne W α β g w hne] at hv
      exact hv
  calc (changedSet (updateAt W α β g w) W0).card
      ≤ (insert (α, β, g) (changedSet W W0)).card := Finset.card_le_card hsub
    _ ≤ (changedSet W W0).card + 1 := Finset.card_insert_le _ _

end Work.LT
