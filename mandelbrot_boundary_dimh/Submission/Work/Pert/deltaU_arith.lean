import Mathlib

namespace Work.Pert

/-- Elementary arithmetic for the `δu` of the `PertCoordClose` assembly: with
`ρ ≤ 1`, `B ≥ 0`, `2000000/ρ ≤ η` and `B ρ ≤ 10⁻⁶` (the output of
`Work.Pert.parab_germ_taylor_near0` with `ε = 10⁻⁶`), the quantity

  `δu = (1/1024 + 2·((ρ/(32η))/ρ + B ρ²)/(ρ - 4/η))·(1024/1023)`

is at most `1/1000`.  Route: `(ρ/(32η))/ρ = 1/(32η)`, `ρ - 4/η ≥ ρ/2`, so
`2·(1/(32η) + Bρ²)/(ρ - 4/η) ≤ 4(1/(32η) + Bρ²)/ρ = 1/(8ηρ) + 4Bρ`, and `ηρ ≥ 2000000`,
`Bρ ≤ 10⁻⁶` give `≤ 10⁻⁸ + 4·10⁻⁶`; multiplying by `1024/1023 ≤ 2` finishes. -/
theorem deltaU_arith {η ρ B : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 ≤ B)
    (hηρ : 2000000 / ρ ≤ η) (hBρ : B * ρ ≤ 1 / 1000000) :
    (1 / 1024 + 2 * ((ρ / (32 * η) / ρ + B * ρ ^ 2) / (ρ - 4 / η))) * (1024 / 1023)
      ≤ 1 / 1000 := by
  -- `2000000/ρ ≤ η` multiplied by `ρ > 0`, hence `ηρ ≥ 2000000` and in particular `ηρ ≥ 8`.
  have hηρ' : (2000000 : ℝ) ≤ η * ρ := (div_le_iff₀ hρ).mp hηρ
  have h8 : (8 : ℝ) ≤ η * ρ := by linarith
  -- `8 ≤ ηρ` gives `4/η ≤ ρ/2`, hence `ρ - 4/η ≥ ρ/2 > 0`.
  have h4 : 4 / η ≤ ρ / 2 := by
    rw [div_le_iff₀ hη]
    nlinarith [h8]
  have hdenpos : (0 : ℝ) < ρ - 4 / η := by linarith
  -- the numerator `1/(32η) + Bρ²` is nonnegative
  have hnum : (0 : ℝ) ≤ 1 / (32 * η) + B * ρ ^ 2 := by positivity
  -- `(ρ/(32η))/ρ = 1/(32η)`
  have hsimple : ρ / (32 * η) / ρ = 1 / (32 * η) := by field_simp
  rw [hsimple]
  -- enlarge the denominator `ρ - 4/η` to `ρ/2`
  have step1 : (1 / (32 * η) + B * ρ ^ 2) / (ρ - 4 / η)
      ≤ (1 / (32 * η) + B * ρ ^ 2) / (ρ / 2) :=
    div_le_div_of_nonneg_left hnum (by linarith : (0 : ℝ) < ρ / 2) (by linarith)
  have step2 : (1 / (32 * η) + B * ρ ^ 2) / (ρ / 2)
      = 2 * (1 / (32 * η) + B * ρ ^ 2) / ρ := by field_simp
  have step3 : 2 * ((1 / (32 * η) + B * ρ ^ 2) / (ρ / 2))
      ≤ 1 / (8 * (η * ρ)) + 4 * (B * ρ) := by
    rw [step2]
    have h : 2 * (2 * (1 / (32 * η) + B * ρ ^ 2) / ρ) = 1 / (8 * (η * ρ)) + 4 * (B * ρ) := by
      field_simp
      ring
    linarith [h]
  have hmain : 2 * ((1 / (32 * η) + B * ρ ^ 2) / (ρ - 4 / η))
      ≤ 1 / (8 * (η * ρ)) + 4 * (B * ρ) :=
    le_trans (by linarith [step1]) step3
  -- numerical bounds on the two terms
  have h1 : 1 / (8 * (η * ρ)) ≤ 1 / 16000000 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [h8]
  have h2 : 4 * (B * ρ) ≤ 4 / 1000000 := by
    have := mul_le_mul_of_nonneg_left hBρ (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  calc (1 / 1024 + 2 * ((1 / (32 * η) + B * ρ ^ 2) / (ρ - 4 / η))) * (1024 / 1023)
      ≤ (1 / 1024 + (1 / (8 * (η * ρ)) + 4 * (B * ρ))) * (1024 / 1023) := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        linarith
    _ ≤ (1 / 1024 + (1 / 16000000 + 4 / 1000000)) * (1024 / 1023) := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        linarith
    _ ≤ 1 / 1000 := by norm_num

end Work.Pert
