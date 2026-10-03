import Mathlib

namespace Work.Repel.R3Level1

set_option linter.unusedVariables false

theorem loc_small {g r₀ η σ₀ δ : ℝ} (hg : 0 < g) (hr₀ : 0 < r₀) (hr₀le : r₀ ≤ 1 / 200)
    (hδ : 0 ≤ δ) (hσ₀ : σ₀ ≤ 64 / η) (hσLbig : 4 / η ≤ g * r₀ / 256)
    (hδcap : δ ≤ g * r₀ / 256) :
    16 * (σ₀ + δ) / g ≤ 1 / (16 * Real.pi) := by
  -- Key: 64/η ≤ g·r₀/16, hence σ₀ ≤ g·r₀/16.
  have hkey : 64 / η ≤ g * r₀ / 16 := by
    by_cases hη : 0 < η
    · calc 64 / η = 16 * (4 / η) := by ring
        _ ≤ 16 * (g * r₀ / 256) := mul_le_mul_of_nonneg_left hσLbig (by norm_num)
        _ = g * r₀ / 16 := by ring
    · have hle : 64 / η ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt hη)
      have hpos : 0 < g * r₀ / 16 := by positivity
      linarith
  have hσ : σ₀ ≤ g * r₀ / 16 := le_trans hσ₀ hkey
  -- Main numeric bound.
  have hmain : 16 * (σ₀ + δ) / g ≤ 17 / 3200 := by
    have h1 : 16 * (σ₀ + δ) / g ≤ r₀ * 17 / 16 := by
      rw [div_le_iff₀ hg]
      nlinarith [hσ, hδcap]
    have h2 : r₀ * 17 / 16 ≤ 17 / 3200 := by nlinarith [hr₀le]
    linarith
  -- 17/3200 ≤ 1/(16π).
  have hfinal : (17 : ℝ) / 3200 ≤ 1 / (16 * Real.pi) := by
    have hp : (1 : ℝ) / 64 ≤ 1 / (16 * Real.pi) := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith [Real.pi_lt_four]
    have h64 : (17 : ℝ) / 3200 ≤ 1 / 64 := by norm_num
    linarith
  exact le_trans hmain hfinal

end Work.Repel.R3Level1
