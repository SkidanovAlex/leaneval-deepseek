import Mathlib

set_option linter.unusedVariables false

namespace Work.Repel.R3Level1

/-- Arithmetic target inequality of the repel assembly (level 1).

Given the scale conditions
`σ₀ ≤ 64/η`, `10⁸ π δ D ≤ g m ρ`, `10⁷ π D / (g m ρ) ≤ η`, `δ₁ ≤ ρ m / 256`,
all with `D, g, m, ρ > 0` and `σ₀, δ ≥ 0`, we have

`64 π D (σ₀ + δ) / g < (1/50) m ρ - δ₁`.

The constants leave a comfortable margin: the left side is bounded by
`(4096/10⁷ + 64/10⁸) m ρ = (41024/10⁸) m ρ`, while the right side is at least
`(1/50 - 1/256) m ρ = (103/6400) m ρ`, and `41024/10⁸ < 103/6400`. -/
theorem htgt_arith {D g m ρ η σ₀ δ δ₁ : ℝ}
    (hD : 0 < D) (hg : 0 < g) (hm : 0 < m) (hρ : 0 < ρ)
    (hδ : 0 ≤ δ) (hσ₀₀ : 0 ≤ σ₀)
    (hσ₀ : σ₀ ≤ 64 / η)
    (hδsmall : 10 ^ 8 * Real.pi * δ * D ≤ g * m * ρ)
    (hηtgt : 10 ^ 7 * Real.pi * D / (g * m * ρ) ≤ η)
    (hδ₁ : δ₁ ≤ ρ * m / 256) :
    64 * Real.pi * D * (σ₀ + δ) / g < (1 / 50) * m * ρ - δ₁ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- `η > 0` follows from `10⁷ π D / (g m ρ) ≤ η`, the left side being positive.
  have hη : 0 < η := by
    have h : 0 < 10 ^ 7 * Real.pi * D / (g * m * ρ) := by positivity
    linarith
  have hK : 0 < g * m * ρ := by positivity
  -- `σ₀ * η ≤ 64`
  have hσ₀η : σ₀ * η ≤ 64 := by
    have h := mul_le_mul_of_nonneg_right hσ₀ (le_of_lt hη)
    have he : (64 : ℝ) / η * η = 64 := div_mul_cancel₀ 64 (ne_of_gt hη)
    linarith
  -- `10⁷ π D ≤ η (g m ρ)`
  have hηK : 10 ^ 7 * Real.pi * D ≤ η * (g * m * ρ) := by
    have h := mul_le_mul_of_nonneg_right hηtgt (le_of_lt hK)
    have he : (10 ^ 7 * Real.pi * D) / (g * m * ρ) * (g * m * ρ)
        = 10 ^ 7 * Real.pi * D := div_mul_cancel₀ _ (ne_of_gt hK)
    linarith
  -- `σ₀ * (10⁷ π D) ≤ 64 (g m ρ)`
  have hσ₀D : σ₀ * (10 ^ 7 * Real.pi * D) ≤ 64 * (g * m * ρ) := by
    calc σ₀ * (10 ^ 7 * Real.pi * D) ≤ σ₀ * (η * (g * m * ρ)) :=
          mul_le_mul_of_nonneg_left hηK hσ₀₀
      _ = (σ₀ * η) * (g * m * ρ) := by ring
      _ ≤ 64 * (g * m * ρ) := mul_le_mul_of_nonneg_right hσ₀η (le_of_lt hK)
  -- `64 π D σ₀ ≤ 4096 (g m ρ) / 10⁷`
  have hA : 64 * Real.pi * D * σ₀ ≤ 4096 * (g * m * ρ) / 10 ^ 7 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 7)]
    nlinarith [hσ₀D]
  -- `64 π D δ ≤ 64 (g m ρ) / 10⁸`
  have hB : 64 * Real.pi * D * δ ≤ 64 * (g * m * ρ) / 10 ^ 8 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 8)]
    nlinarith [hδsmall]
  have hmain : 64 * Real.pi * D * (σ₀ + δ) ≤ (41024 / 10 ^ 8) * (g * m * ρ) := by
    nlinarith [hA, hB]
  have hδ₁g : δ₁ * g ≤ ρ * m / 256 * g := mul_le_mul_of_nonneg_right hδ₁ (le_of_lt hg)
  have hright : (103 / 6400) * (g * m * ρ) ≤ ((1 / 50) * m * ρ - δ₁) * g := by
    nlinarith [hδ₁g]
  rw [div_lt_iff₀ hg]
  have hnum : (41024 / 10 ^ 8 : ℝ) < 103 / 6400 := by norm_num
  have hmono : (41024 / 10 ^ 8) * (g * m * ρ) < (103 / 6400) * (g * m * ρ) :=
    mul_lt_mul_of_pos_right hnum hK
  linarith [hmain, hmono, hright]

end Work.Repel.R3Level1
