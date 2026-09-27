import Mathlib
import Submission.Work.Geo.DualStretch.Defs

set_option linter.unusedVariables false

namespace Work.Geo.DualStretch

/-- `massOf s μ τ` is `max 0 (card τ * (minVal τ μ - maxVal (s \ τ) μ))`; it is positive exactly
when `τ` is nonempty and the level value of `τ` strictly exceeds every value outside `τ`. -/
theorem massOf_pos_iff {n : ℕ} {s τ : Finset (PL.E n)} {μ : PL.E n → ℝ} (hτ : τ ⊆ s) :
    0 < Work.Geo.DualStretch.massOf s μ τ ↔
      τ.Nonempty ∧ Work.Geo.DualStretch.maxVal (s \ τ) μ < Work.Geo.DualStretch.minVal τ μ := by
  rw [Work.Geo.DualStretch.massOf]
  constructor
  · intro h
    rw [lt_max_iff] at h
    rcases h with h | h
    · exact absurd h (lt_irrefl 0)
    · have hD : 0 < Work.Geo.DualStretch.minVal τ μ - Work.Geo.DualStretch.maxVal (s \ τ) μ :=
        pos_of_mul_pos_right h (Nat.cast_nonneg _)
      have hc : (0 : ℝ) < (τ.card : ℝ) := pos_of_mul_pos_left h (le_of_lt hD)
      exact ⟨Finset.card_pos.mp (by exact_mod_cast hc), sub_pos.mp hD⟩
  · rintro ⟨hne, hlt⟩
    rw [lt_max_iff]
    exact Or.inr (mul_pos (by exact_mod_cast Finset.card_pos.mpr hne) (sub_pos.mpr hlt))

end Work.Geo.DualStretch
