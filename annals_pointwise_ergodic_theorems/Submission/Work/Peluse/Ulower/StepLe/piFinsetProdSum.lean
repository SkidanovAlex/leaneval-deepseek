import Mathlib

namespace Work.Peluse.Ulower.StepLe

/-- Summing a function of the two coordinates over the box `Q ×ˢ Q` in every coordinate of
`Fin k` is the same as summing it over the two independent `Fin k`-tuples of elements of `Q`.
This is the reindexing
`(Fin k → ℤ) × (Fin k → ℤ) ≃ (Fin k → ℤ × ℤ)`, `(u, v) ↦ fun i ↦ (u i, v i)`. -/
lemma piFinsetProdSum {k : ℕ} (Q : Finset ℤ) (g : (Fin k → ℤ) → (Fin k → ℤ) → ℝ) :
    (∑ H ∈ Fintype.piFinset (fun _ : Fin k => Q.product Q), g (fun i => (H i).1) (fun i => (H i).2))
      = ∑ u ∈ Fintype.piFinset (fun _ : Fin k => Q), ∑ v ∈ Fintype.piFinset (fun _ : Fin k => Q), g u v := by
  classical
  set A : Finset (Fin k → ℤ) := Fintype.piFinset (fun _ : Fin k => Q) with hA
  -- Reindex the left-hand side by the bijection with `A ×ˢ A`.
  have key : (∑ H ∈ Fintype.piFinset (fun _ : Fin k => Q.product Q),
        g (fun i => (H i).1) (fun i => (H i).2)) = ∑ p ∈ A ×ˢ A, g p.1 p.2 := by
    refine Finset.sum_bij (fun H _ => ((fun i => (H i).1), (fun i => (H i).2))) ?_ ?_ ?_ ?_
    · -- the image lies in `A ×ˢ A`
      intro H hH
      rw [Finset.mem_product]
      constructor
      · rw [Fintype.mem_piFinset]
        intro i
        exact (Finset.mem_product.mp (Fintype.mem_piFinset.mp hH i)).1
      · rw [Fintype.mem_piFinset]
        intro i
        exact (Finset.mem_product.mp (Fintype.mem_piFinset.mp hH i)).2
    · -- injectivity
      intro H hH K hK h
      funext i
      exact Prod.ext (congr_fun (Prod.mk.inj h).1 i) (congr_fun (Prod.mk.inj h).2 i)
    · -- surjectivity
      rintro ⟨u, v⟩ hp
      rw [Finset.mem_product] at hp
      refine ⟨fun i => (u i, v i), ?_, ?_⟩
      · rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hp.1 i, Fintype.mem_piFinset.mp hp.2 i⟩
      · rfl
    · -- the summands agree
      intro H hH
      rfl
  rw [key]
  exact Finset.sum_product A A (fun p => g p.1 p.2)

end Work.Peluse.Ulower.StepLe
