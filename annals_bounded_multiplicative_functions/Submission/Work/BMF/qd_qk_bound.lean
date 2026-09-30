import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem qd_qk_bound {c₀ Cπ π₁ π₂ M : ℝ} (hc₀ : 0 < c₀) (hCπ : 0 < Cπ)
    (hπ₁ : π₁ ≥ Cπ / (20 * c₀ ^ 3) + 1) (hπ₂ : 0 < π₂) (hM : 0 < M) :
    20 * c₀ ^ 6 * π₁ ^ 2 * π₂ * M / Cπ
      ≤ (c₀ ^ 3 * π₁ * π₂ * M) ^ 2 / ((M / 40) * (Cπ * π₂)) - c₀ ^ 3 * π₁ * π₂ * M := by
  -- π₁ > 0 from the lower bound
  have hπ₁pos : 0 < π₁ := by
    have : 0 < Cπ / (20 * c₀ ^ 3) := by positivity
    linarith
  -- the essential arithmetic content: Cπ ≤ 20 c₀³ π₁
  have hCπle : Cπ ≤ 20 * c₀ ^ 3 * π₁ := by
    have h1 : Cπ / (20 * c₀ ^ 3) + 1 ≤ π₁ := hπ₁
    have h16 : (0 : ℝ) ≤ 20 * c₀ ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left h1 h16
    have heq : (20 * c₀ ^ 3) * (Cπ / (20 * c₀ ^ 3) + 1) = Cπ + 20 * c₀ ^ 3 := by
      field_simp
    rw [heq] at hmul
    linarith
  -- hence 20 c₀³ π₁ / Cπ - 1 ≥ 0, and the difference rewrites to
  -- c₀³ π₁ π₂ M * (20 c₀³ π₁ / Cπ - 1)
  have hfac : 0 ≤ 20 * c₀ ^ 3 * π₁ / Cπ - 1 := by
    have h1 : (1 : ℝ) ≤ 20 * c₀ ^ 3 * π₁ / Cπ := (one_le_div hCπ).mpr hCπle
    linarith
  have hpos : 0 ≤ c₀ ^ 3 * π₁ * π₂ * M := by positivity
  have hDn : 0 ≤ c₀ ^ 3 * π₁ * π₂ * M * (20 * c₀ ^ 3 * π₁ / Cπ - 1) :=
    mul_nonneg hpos hfac
  have hDeq : (c₀ ^ 3 * π₁ * π₂ * M) ^ 2 / ((M / 40) * (Cπ * π₂)) - c₀ ^ 3 * π₁ * π₂ * M
        - 20 * c₀ ^ 6 * π₁ ^ 2 * π₂ * M / Cπ
      = c₀ ^ 3 * π₁ * π₂ * M * (20 * c₀ ^ 3 * π₁ / Cπ - 1) := by
    have hCπne : Cπ ≠ 0 := ne_of_gt hCπ
    have hMne : M ≠ 0 := ne_of_gt hM
    have hπ₂ne : π₂ ≠ 0 := ne_of_gt hπ₂
    field_simp
    ring
  linarith [hDeq, hDn]

end Work.BMF
