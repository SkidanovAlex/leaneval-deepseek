import Mathlib

namespace Work.FIArea2

theorem section_set_eq (M C u : ℝ) :
    {t : ℝ | |u ^ 2 - t ^ 2| ≤ 2 * Real.sqrt M ∧ u ^ 2 + t ^ 2 ≤ C}
      = {t : ℝ | max 0 (u ^ 2 - 2 * Real.sqrt M) ≤ t ^ 2 ∧
            t ^ 2 ≤ min (u ^ 2 + 2 * Real.sqrt M) (C - u ^ 2)} := by
  ext t
  simp only [abs_le, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨sq_nonneg t, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨-, h1⟩, h2, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

end Work.FIArea2
