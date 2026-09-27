import Mathlib

namespace Work.KT

/-- A continuous family of complex matrices over a compact space is uniformly bounded: there is a
bound on the entrywise-sup norm of `2 * γ x - 1`. -/
theorem chain_exists_norm_bound {X : Type*} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (γ : X → Matrix (Fin n) (Fin n) ℂ) (hγ : Continuous γ) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ x : X,
      ‖(fun i j => ((2 * γ x - 1 : Matrix (Fin n) (Fin n) ℂ)) i j)‖ ≤ A₀ := by
  have hcont : Continuous
      (fun x : X => ‖(fun i j => ((2 * γ x - 1 : Matrix (Fin n) (Fin n) ℂ)) i j)‖) := by
    fun_prop
  have hbdd : BddAbove (Set.range
      fun x : X => ‖(fun i j => ((2 * γ x - 1 : Matrix (Fin n) (Fin n) ℂ)) i j)‖) := by
    simpa [Set.image_univ] using (isCompact_univ.image hcont).bddAbove
  rw [bddAbove_def] at hbdd
  obtain ⟨A, hA⟩ := hbdd
  exact ⟨max A 0, le_max_right _ _,
    fun x => le_trans (hA _ (Set.mem_range_self x)) (le_max_left _ _)⟩

end Work.KT
