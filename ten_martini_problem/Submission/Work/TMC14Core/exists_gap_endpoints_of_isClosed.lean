import Mathlib

namespace Work.TMC14Core

theorem exists_gap_endpoints_of_isClosed {U : Set ℝ} (hU : IsClosed U) {c d E : ℝ}
    (hE : E ∉ U) (hcE : c ≤ E) (hEd : E ≤ d) (hcd : c < d) :
    ∃ a' b' : ℝ, a' ≤ E ∧ E ≤ b' ∧ b' ≤ d ∧
      (∀ y ∈ Set.Ioo a' b', y ∉ U) ∧ (c ≤ a' → a' ∈ U) ∧ (b' < d → b' ∈ U) := by
  by_cases hP : ∃ x ∈ U, x ≤ E
  · -- There is a point of U at or below E: take A = greatest such point.
    obtain ⟨x0, hx0U, hx0E⟩ := hP
    have hSclosed : IsClosed (U ∩ Set.Iic E) := hU.inter isClosed_Iic
    have hSne : (U ∩ Set.Iic E).Nonempty := ⟨x0, hx0U, hx0E⟩
    have hSbdd : BddAbove (U ∩ Set.Iic E) := ⟨E, fun y hy => hy.2⟩
    set A : ℝ := sSup (U ∩ Set.Iic E) with hA
    have hAg : IsGreatest (U ∩ Set.Iic E) A := by
      rw [hA]; exact hSclosed.isGreatest_csSup hSne hSbdd
    have hAU : A ∈ U := hAg.1.1
    have hAle : A ≤ E := hAg.1.2
    have hAub : ∀ y, y ∈ U → y ≤ E → y ≤ A := fun y hyU hyE => hAg.2 ⟨hyU, hyE⟩
    have hAlt : A < E := lt_of_le_of_ne hAle (fun h => hE (h ▸ hAU))
    by_cases hQ : ∃ x ∈ U, E ≤ x
    · -- There is a point of U at or above E: take B = least such point, clip by d.
      obtain ⟨y0, hy0U, hy0E⟩ := hQ
      have hS'closed : IsClosed (U ∩ Set.Ici E) := hU.inter isClosed_Ici
      have hS'ne : (U ∩ Set.Ici E).Nonempty := ⟨y0, hy0U, hy0E⟩
      have hS'bdd : BddBelow (U ∩ Set.Ici E) := ⟨E, fun y hy => hy.2⟩
      set B : ℝ := sInf (U ∩ Set.Ici E) with hB
      have hBl : IsLeast (U ∩ Set.Ici E) B := by
        rw [hB]; exact hS'closed.isLeast_csInf hS'ne hS'bdd
      have hBU : B ∈ U := hBl.1.1
      have hBeE : E ≤ B := hBl.1.2
      have hBlb : ∀ y, y ∈ U → E ≤ y → B ≤ y := fun y hyU hyE => hBl.2 ⟨hyU, hyE⟩
      have hfree : ∀ y ∈ Set.Ioo A (min d B), y ∉ U := by
        intro y hy hyU
        rw [Set.mem_Ioo] at hy
        have hyB : y < B := lt_of_lt_of_le hy.2 (min_le_right _ _)
        by_cases hyE : y ≤ E
        · exact absurd (hAub y hyU hyE) (not_le.mpr hy.1)
        · exact absurd (hBlb y hyU (le_of_not_ge hyE)) (not_le.mpr hyB)
      have hc2 : min d B < d → min d B ∈ U := by
        intro h
        have hBd : B < d := by
          rcases min_lt_iff.mp h with h' | h'
          · exact absurd h' (lt_irrefl d)
          · exact h'
        rw [min_eq_right (le_of_lt hBd)]
        exact hBU
      exact ⟨A, min d B, hAle, le_min hEd hBeE, min_le_left _ _, hfree,
        fun _ => hAU, hc2⟩
    · -- No point of U at or above E: b' = d.
      have hfree : ∀ y ∈ Set.Ioo A d, y ∉ U := by
        intro y hy hyU
        rw [Set.mem_Ioo] at hy
        by_cases hyE : y ≤ E
        · exact absurd (hAub y hyU hyE) (not_le.mpr hy.1)
        · exact absurd ⟨y, hyU, le_of_not_ge hyE⟩ hQ
      exact ⟨A, d, hAle, hEd, le_refl d, hfree, fun _ => hAU,
        fun h => absurd h (lt_irrefl d)⟩
  · -- No point of U at or below E.
    have hPnole : ∀ y, y ∈ U → ¬ (y ≤ E) := fun y hyU hyE => hP ⟨y, hyU, hyE⟩
    have ha'le : c - 1 ≤ E := by linarith
    have hca' : ¬ (c ≤ c - 1) := by linarith
    by_cases hQ : ∃ x ∈ U, E ≤ x
    · obtain ⟨y0, hy0U, hy0E⟩ := hQ
      have hS'closed : IsClosed (U ∩ Set.Ici E) := hU.inter isClosed_Ici
      have hS'ne : (U ∩ Set.Ici E).Nonempty := ⟨y0, hy0U, hy0E⟩
      have hS'bdd : BddBelow (U ∩ Set.Ici E) := ⟨E, fun y hy => hy.2⟩
      set B : ℝ := sInf (U ∩ Set.Ici E) with hB
      have hBl : IsLeast (U ∩ Set.Ici E) B := by
        rw [hB]; exact hS'closed.isLeast_csInf hS'ne hS'bdd
      have hBU : B ∈ U := hBl.1.1
      have hBeE : E ≤ B := hBl.1.2
      have hBlb : ∀ y, y ∈ U → E ≤ y → B ≤ y := fun y hyU hyE => hBl.2 ⟨hyU, hyE⟩
      have hfree : ∀ y ∈ Set.Ioo (c - 1) (min d B), y ∉ U := by
        intro y hy hyU
        rw [Set.mem_Ioo] at hy
        have hyB : y < B := lt_of_lt_of_le hy.2 (min_le_right _ _)
        by_cases hyE : y ≤ E
        · exact absurd hyE (hPnole y hyU)
        · exact absurd (hBlb y hyU (le_of_not_ge hyE)) (not_le.mpr hyB)
      have hc2 : min d B < d → min d B ∈ U := by
        intro h
        have hBd : B < d := by
          rcases min_lt_iff.mp h with h' | h'
          · exact absurd h' (lt_irrefl d)
          · exact h'
        rw [min_eq_right (le_of_lt hBd)]
        exact hBU
      exact ⟨c - 1, min d B, ha'le, le_min hEd hBeE, min_le_left _ _, hfree,
        fun h => absurd h hca', hc2⟩
    · have hfree : ∀ y ∈ Set.Ioo (c - 1) d, y ∉ U := by
        intro y hy hyU
        rw [Set.mem_Ioo] at hy
        rcases lt_or_ge y E with hyE | hyE
        · exact absurd (le_of_lt hyE) (hPnole y hyU)
        · exact absurd ⟨y, hyU, hyE⟩ hQ
      exact ⟨c - 1, d, ha'le, hEd, le_refl d, hfree, fun h => absurd h hca',
        fun h => absurd h (lt_irrefl d)⟩

end Work.TMC14Core
