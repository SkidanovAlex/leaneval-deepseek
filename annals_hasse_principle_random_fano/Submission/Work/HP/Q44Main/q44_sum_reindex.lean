import Mathlib

namespace Work.HP.Q44Main

/-- The sum over the dependent product of functions `Fin 3 → ℕ` taking values in a common
finset `s` reindexes as the corresponding triple iterated sum. -/
theorem q44_sum_reindex_aux (s : Finset ℕ) (g : ℕ → ℕ → ℕ → ℝ) :
    (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => s), g (k 0) (k 1) (k 2))
    = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, g a b c := by
  have key : (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => s), g (k 0) (k 1) (k 2))
      = ∑ p ∈ s ×ˢ (s ×ˢ s), g p.1 p.2.1 p.2.2 := by
    refine Finset.sum_bij' (fun k _ => (k 0, (k 1, k 2))) (fun p _ => ![p.1, p.2.1, p.2.2])
      ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Fintype.mem_piFinset] at hk
      simp only [Finset.mem_product]
      exact ⟨hk 0, hk 1, hk 2⟩
    · intro p hp
      rw [Fintype.mem_piFinset]
      simp only [Finset.mem_product] at hp
      intro i
      fin_cases i
      · exact hp.1
      · exact hp.2.1
      · exact hp.2.2
    · intro k _
      funext i
      fin_cases i <;> simp
    · intro p _
      cases p with
      | mk a q => cases q with
        | mk b c => rfl
    · intro k _
      rfl
  rw [key]
  simp only [Finset.sum_product]

theorem q44_sum_reindex (N : ℕ) (g : ℕ → ℕ → ℕ → ℝ) :
    (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)), g (k 0) (k 1) (k 2))
    = ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), ∑ c ∈ Finset.range (N + 1), g a b c :=
  q44_sum_reindex_aux (Finset.range (N + 1)) g

end Work.HP.Q44Main
