import Mathlib
import Submission.Work.OddRadon.RadialDefs

namespace Work.OddRadon

theorem radialSystem_iff_div (n : ℕ) {Φ Ψ : ℝ → ℝ} {R r : ℝ → ℝ} :
    RadialSystem n Φ Ψ R r ↔
      ((∀ α ∈ Set.Ico 0 (Real.pi / 2),
          R α ^ (2 * n + 2) + r α ^ (2 * n + 2) = Φ α / Real.cos α ^ 2 ∧
            R α ^ (2 * n + 1) - r α ^ (2 * n + 1) = Ψ α / Real.cos α) ∧
        Φ (Real.pi / 2) = 0 ∧ Ψ (Real.pi / 2) = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro α hα
      have hcpos : 0 < Real.cos α :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hα.1, Real.pi_pos], by linarith [hα.2]⟩
      have hc : Real.cos α ≠ 0 := ne_of_gt hcpos
      obtain ⟨h1, h2⟩ := h α ⟨hα.1, le_of_lt hα.2⟩
      refine ⟨?_, ?_⟩
      · rw [eq_div_iff (pow_ne_zero 2 hc)]; exact h1
      · rw [eq_div_iff hc]; exact h2
    · have := (h (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_refl _⟩).1
      rw [Real.cos_pi_div_two] at this; simpa using this.symm
    · have := (h (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_refl _⟩).2
      rw [Real.cos_pi_div_two] at this; simpa using this.symm
  · rintro ⟨hdiv, hΦ, hΨ⟩ α hα
    rcases lt_or_eq_of_le hα.2 with hlt | heq
    · have hcpos : 0 < Real.cos α :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hα.1, Real.pi_pos], by linarith [hlt]⟩
      have hc : Real.cos α ≠ 0 := ne_of_gt hcpos
      obtain ⟨h1, h2⟩ := hdiv α ⟨hα.1, hlt⟩
      rw [eq_div_iff (pow_ne_zero 2 hc)] at h1
      rw [eq_div_iff hc] at h2
      exact ⟨h1, h2⟩
    · rw [heq, Real.cos_pi_div_two]
      exact ⟨by simp [hΦ], by simp [hΨ]⟩

end Work.OddRadon
