import Mathlib

namespace Work.Drive

/-- A continuous positive function on a closed annulus `{z : ℂ | ρ ≤ ‖z‖ ≤ σ}` is bounded below
by a positive constant: the annulus is compact (closed and bounded) when nonempty, and empty
otherwise. -/
theorem exists_pos_le_on_annulus {F : ℂ → ℝ} (hF : Continuous F) {ρ σ : ℝ}
    (hpos : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ σ → 0 < F z) :
    ∃ q : ℝ, 0 < q ∧ ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ σ → q ≤ F z := by
  by_cases hρσ : ρ ≤ σ
  · by_cases hσ : 0 ≤ σ
    · have hnorm : ‖(σ : ℂ)‖ = σ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ]
      have hne : ({z : ℂ | ρ ≤ ‖z‖ ∧ ‖z‖ ≤ σ} : Set ℂ).Nonempty :=
        ⟨(σ : ℂ), by rw [hnorm]; exact hρσ, by rw [hnorm]⟩
      have hcl : IsClosed ({z : ℂ | ρ ≤ ‖z‖ ∧ ‖z‖ ≤ σ} : Set ℂ) := by
        have h1 : IsClosed ({z : ℂ | ρ ≤ ‖z‖} : Set ℂ) :=
          isClosed_le continuous_const continuous_norm
        have h2 : IsClosed ({z : ℂ | ‖z‖ ≤ σ} : Set ℂ) :=
          isClosed_le continuous_norm continuous_const
        exact h1.inter h2
      have hsub : ({z : ℂ | ρ ≤ ‖z‖ ∧ ‖z‖ ≤ σ} : Set ℂ) ⊆ Metric.closedBall 0 σ := by
        intro z hz
        simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact hz.2
      have hK : IsCompact ({z : ℂ | ρ ≤ ‖z‖ ∧ ‖z‖ ≤ σ} : Set ℂ) :=
        (isCompact_closedBall (0 : ℂ) σ).of_isClosed_subset hcl hsub
      obtain ⟨z1, hz1, hmin⟩ := hK.exists_isMinOn hne hF.continuousOn
      exact ⟨F z1, hpos z1 hz1.1 hz1.2, fun z h1 h2 => hmin ⟨h1, h2⟩⟩
    · exact ⟨1, one_pos, fun z _ h2 => absurd (le_trans (norm_nonneg z) h2) hσ⟩
  · exact ⟨1, one_pos, fun z h1 h2 => absurd (le_trans h1 h2) hρσ⟩

end Work.Drive
