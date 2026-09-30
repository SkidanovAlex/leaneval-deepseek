import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem qd_small_c_modulus {c c₀ Cπ π₁ π₂ M : ℝ} (hc : 0 < c) (hc₀ : 0 < c₀) (hCπ : 0 < Cπ)
    (hπ₁ : π₁ ≥ Cπ / (20 * c₀ ^ 3) + 1) (hπ₂ : 0 < π₂) (hM : 0 < M)
    (hc2 : c ≤ 200 * c₀ ^ 6 / Cπ ^ 3) :
    c * (2 * π₂) * (2 * ((M / 40) * (Cπ * π₁) ^ 2))
      ≤ (c₀ ^ 3 * π₁ * π₂ * M) ^ 2 / ((M / 40) * (Cπ * π₂)) - c₀ ^ 3 * π₁ * π₂ * M := by
  -- π₁ is positive, since `Cπ / (20 * c₀ ^ 3) > 0`.
  have hπ1pos : 0 < π₁ := by
    have h : 0 < Cπ / (20 * c₀ ^ 3) := by positivity
    linarith
  -- Clear the denominator in `hc2`: `c * Cπ ^ 3 ≤ 200 * c₀ ^ 6`.
  have hCπ3 : 0 < Cπ ^ 3 := by positivity
  have hcCπ : c * Cπ ^ 3 ≤ 200 * c₀ ^ 6 := by
    have := (le_div_iff₀ hCπ3).mp hc2
    linarith
  -- Clear the denominator in `hπ₁`: `Cπ ≤ 20 * c₀ ^ 3 * π₁`.
  have hCπle : Cπ ≤ 20 * c₀ ^ 3 * π₁ := by
    have h : Cπ / (20 * c₀ ^ 3) ≤ π₁ := by linarith
    have := (div_le_iff₀ (show (0 : ℝ) < 20 * c₀ ^ 3 by positivity)).mp h
    linarith
  -- The key polynomial inequality, obtained by adding the two cleaned-up bounds.
  have hkey : c * Cπ ^ 3 * π₁ ≤ 400 * c₀ ^ 6 * π₁ - 10 * c₀ ^ 3 * Cπ := by
    have h1 : c * Cπ ^ 3 * π₁ ≤ 200 * c₀ ^ 6 * π₁ := by nlinarith [hcCπ, hπ1pos]
    have h2 : 10 * c₀ ^ 3 * Cπ ≤ 200 * c₀ ^ 6 * π₁ := by nlinarith [hCπle, hc₀]
    linarith
  -- Clear the denominator `(M / 40) * (Cπ * π₂) > 0` on the right-hand side.
  have hg : 0 < (M / 40) * (Cπ * π₂) := by positivity
  rw [le_sub_iff_add_le, le_div_iff₀ hg]
  -- The remaining goal is polynomial; `hkey` scaled by the positive monomial
  -- `π₁ * π₂ ^ 2 * M ^ 2 / 400` closes it.
  have hkey2 :=
    mul_le_mul_of_nonneg_right hkey (show (0 : ℝ) ≤ π₁ * π₂ ^ 2 * M ^ 2 / 400 by positivity)
  nlinarith [hkey2]

end Work.BMF
