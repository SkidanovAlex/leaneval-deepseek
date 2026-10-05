import Mathlib

namespace Work.RPB.B2

theorem chordSurf_inj_endgame {t r r' t' : ℝ} {m₁ m₂ : ℤ}
    (hr : 0 < r) (hrπ : r < Real.pi) (hr' : 0 < r') (hr'π : r' < Real.pi)
    (h₁ : t' + r' = t + r + 2 * Real.pi * (m₁ : ℝ))
    (h₂ : t' - r' = t - r + 2 * Real.pi * (m₂ : ℝ)) :
    r' = r ∧ ∃ m : ℤ, t' = t + 2 * Real.pi * (m : ℝ) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  -- Subtracting the two relations isolates the difference `r' - r`:
  -- `2 (r' - r) = 2π (m₁ - m₂)`, hence `r' - r = π (m₁ - m₂)`.
  have hdiff : r' - r = Real.pi * ((m₁ - m₂ : ℤ) : ℝ) := by
    have h : 2 * (r' - r) = 2 * (Real.pi * ((m₁ - m₂ : ℤ) : ℝ)) := by
      have hcast : ((m₁ - m₂ : ℤ) : ℝ) = (m₁ : ℝ) - (m₂ : ℝ) := by push_cast; ring
      rw [hcast]; linarith
    linarith
  have hkey : Real.pi * ((m₁ - m₂ : ℤ) : ℝ) = r' - r := hdiff.symm
  -- Since `r, r' ∈ (0, π)` we have `|r' - r| < π`, so `|π (m₁ - m₂)| < π`,
  -- i.e. `-1 < m₁ - m₂ < 1` in `ℤ`, forcing `m₁ = m₂`.
  have hlt_k : ((m₁ - m₂ : ℤ) : ℝ) < 1 := by
    nlinarith [hpi, hr', hr'π, hkey]
  have hgt_k : (-1:ℝ) < ((m₁ - m₂ : ℤ) : ℝ) := by
    nlinarith [hpi, hr, hrπ, hkey]
  have hk_zero : m₁ - m₂ = 0 := by
    have h1 : m₁ - m₂ < 1 := by exact_mod_cast hlt_k
    have h2 : -1 < m₁ - m₂ := by exact_mod_cast hgt_k
    omega
  have hr_eq : r' = r := by
    have : r' - r = 0 := by
      rw [hdiff, hk_zero]; push_cast; ring
    linarith
  -- With `r' = r`, the first relation gives `t' = t + 2π m₁`.
  exact ⟨hr_eq, m₁, by linarith⟩

end Work.RPB.B2
