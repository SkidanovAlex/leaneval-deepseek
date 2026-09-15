import Mathlib.Data.Finset.Insert
import Mathlib.Data.Real.Basic

namespace Commons.Analysis.Order

/-- A finite family of "eventually in `R`" properties, each with a threshold `≥ 3`, has a common
threshold: if for every `i ∈ s` there is `R₀ ≥ 3` such that `P i R` holds for all `R ≥ R₀`, then
there is a single `R₀ ≥ 3` such that `P i R` holds for all `i ∈ s` and all `R ≥ R₀`.

Suggested proof: induction on the finset (`Finset.induction_on`), combining two thresholds with
`max` and `max_le`, or directly via `Finset.sup'` with `Finset.le_sup'` and `Finset.sup'_le`. -/
theorem exists_threshold_finset {ι : Type*} (s : Finset ι) (P : ι → ℝ → Prop)
    (h : ∀ i ∈ s, ∃ R₀ : ℝ, 3 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → P i R) :
    ∃ R₀ : ℝ, 3 ≤ R₀ ∧ ∀ i ∈ s, ∀ R : ℝ, R₀ ≤ R → P i R := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨3, le_refl 3, by simp⟩
  | insert a s ha ih =>
    obtain ⟨R₀, hR₀3, hR₀⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨R₁, hR₁3, hR₁⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨max R₀ R₁, le_max_of_le_left hR₀3, ?_⟩
    intro i hi R hR
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hR₀ R (le_trans (le_max_left _ _) hR)
    · exact hR₁ i hi R (le_trans (le_max_right _ _) hR)

end Commons.Analysis.Order