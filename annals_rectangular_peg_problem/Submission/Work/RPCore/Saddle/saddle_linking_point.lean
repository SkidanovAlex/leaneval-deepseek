import Mathlib
import Submission.Work.RPCore.Saddle.linking_no_escape

namespace Work.RPCore.Saddle

theorem saddle_linking_point {k l : ℕ} (a₀ ρ : ℝ) (hρ : 0 < ρ)
    (γ : EuclideanSpace ℝ (Fin k) → ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)))
    (hγ : Continuous γ) (hbc : ∀ u, ‖u‖ = 1 → γ u = (a₀, (ρ • u, 0))) :
    ∃ u : EuclideanSpace ℝ (Fin k), ‖u‖ ≤ 1 ∧ (γ u).2.1 = 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- In dimension `0` the space is a subsingleton, so the middle component vanishes everywhere.
    subst hk
    exact ⟨0, by simp, Subsingleton.elim _ _⟩
  · -- Rescale the middle component by `ρ⁻¹` to reduce to the `ρ = 1` statement.
    have hρne : ρ ≠ 0 := ne_of_gt hρ
    obtain ⟨u, hu, hzu⟩ := linking_no_escape (k := k) hk a₀
      (fun u => (a₀, (ρ⁻¹ • (γ u).2.1, (γ u).2.2)))
      (Continuous.prodMk continuous_const
        (Continuous.prodMk ((hγ.snd.fst).const_smul (ρ⁻¹)) hγ.snd.snd))
      (fun u hu1 => by
        rw [hbc u hu1]
        exact Prod.ext rfl (Prod.ext (inv_smul_smul₀ hρne u) rfl))
    refine ⟨u, hu, ?_⟩
    have h2 : ρ⁻¹ • (γ u).2.1 = 0 := hzu
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h (inv_ne_zero hρne)
    · exact h

end Work.RPCore.Saddle
