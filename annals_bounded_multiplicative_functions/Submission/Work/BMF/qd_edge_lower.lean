import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Elementary real inequality used at the "edge" of the `Q`-data range: if `c` is bounded by
`5 c₀ ^ 6 / (2 Cπ ^ 2)` and `π₁ ≥ Cπ / (20 c₀ ^ 3) + 1`, then the lower bound for the quadratic
`x ↦ x ^ 2 / ((M/40) (Cπ π₂)) - x` at `x = c₀ ^ 3 π₁ π₂ M` dominates the linear term
`c (4 π₁ ^ 2 M) (2 Cπ π₂)`. -/
theorem qd_edge_lower {c c₀ Cπ π₁ π₂ M : ℝ} (hc : 0 < c) (hc₀ : 0 < c₀) (hCπ : 0 < Cπ)
    (hπ₁ : π₁ ≥ Cπ / (20 * c₀ ^ 3) + 1) (hπ₂ : 0 < π₂) (hM : 0 < M)
    (hc1 : c ≤ 5 * c₀ ^ 6 / (2 * Cπ ^ 2)) :
    c * (4 * π₁ ^ 2 * M) * (2 * (Cπ * π₂))
      ≤ (c₀ ^ 3 * π₁ * π₂ * M) ^ 2 / ((M / 40) * (Cπ * π₂)) - c₀ ^ 3 * π₁ * π₂ * M := by
  have hc0pos : (0 : ℝ) < c₀ ^ 3 := by positivity
  have h20 : (0 : ℝ) < 20 * c₀ ^ 3 := by positivity
  -- `π₁ > 0`
  have hpi1pos : 0 < π₁ := by
    have : 0 ≤ Cπ / (20 * c₀ ^ 3) := by positivity
    linarith
  -- clear the division in the hypothesis on `π₁`
  have hπ₁' : Cπ + 20 * c₀ ^ 3 ≤ 20 * c₀ ^ 3 * π₁ := by
    have h1 : Cπ / (20 * c₀ ^ 3) ≤ π₁ - 1 := by linarith
    have h2 : Cπ ≤ (π₁ - 1) * (20 * c₀ ^ 3) := (div_le_iff₀ h20).mp h1
    nlinarith [h2]
  -- clear the division in the hypothesis on `c`
  have h2Cπ : (0 : ℝ) < 2 * Cπ ^ 2 := by positivity
  have hc1' : c * (2 * Cπ ^ 2) ≤ 5 * c₀ ^ 6 := (le_div_iff₀ h2Cπ).mp hc1
  -- the key reduced inequality
  have key : 8 * c * Cπ ^ 2 * π₁ + c₀ ^ 3 * Cπ ≤ 40 * c₀ ^ 6 * π₁ := by
    nlinarith [hc1', hπ₁', hpi1pos, hc0pos, hc]
  have hD : 0 < (M / 40) * (Cπ * π₂) := by positivity
  rw [le_sub_iff_add_le]
  rw [le_div_iff₀ hD]
  have hfac : (0 : ℝ) ≤ π₁ * π₂ ^ 2 * M ^ 2 / 40 := by positivity
  have key2 := mul_le_mul_of_nonneg_right key hfac
  calc
    (c * (4 * π₁ ^ 2 * M) * (2 * (Cπ * π₂)) + c₀ ^ 3 * π₁ * π₂ * M) * ((M / 40) * (Cπ * π₂))
        = (8 * c * Cπ ^ 2 * π₁ + c₀ ^ 3 * Cπ) * (π₁ * π₂ ^ 2 * M ^ 2 / 40) := by ring
    _ ≤ 40 * c₀ ^ 6 * π₁ * (π₁ * π₂ ^ 2 * M ^ 2 / 40) := key2
    _ = (c₀ ^ 3 * π₁ * π₂ * M) ^ 2 := by ring

end Work.BMF
