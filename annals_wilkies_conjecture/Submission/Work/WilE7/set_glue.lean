import Mathlib
import Submission.Work.WilE7.Defs

namespace Work.WilE7

theorem set_glue :
    (∀ {n : ℕ} (s : Finset (Set (Fin n → ℝ))),
        (⋃ i ∈ s, i) = ⋃₀ (s : Set (Set (Fin n → ℝ)))) ∧
    (∀ {n : ℕ} {κ : Set (Fin n → ℝ)}, IsPreconnected κ →
        ∀ {X : Set (Fin n → ℝ)} {p : Fin n → ℝ}, κ ⊆ X →
          κ ⊆ connectedComponentIn X p ∨ Disjoint κ (connectedComponentIn X p)) ∧
    (∀ {n : ℕ} {C : Finset (Set (Fin n → ℝ))} {z : Fin n → ℝ},
        z ∈ ⋃₀ (C : Set (Set (Fin n → ℝ))) ↔ ∃ κ ∈ C, z ∈ κ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n s
    ext x
    simp
  · intro n κ hκ X p hκX
    by_cases h : Disjoint κ (connectedComponentIn X p)
    · exact Or.inr h
    · refine Or.inl ?_
      obtain ⟨y, hyκ, hycc⟩ := Set.not_disjoint_iff.mp h
      rw [connectedComponentIn_eq hycc]
      exact IsPreconnected.subset_connectedComponentIn hκ hyκ hκX
  · intro n C z
    simp [Set.mem_sUnion]

end Work.WilE7
