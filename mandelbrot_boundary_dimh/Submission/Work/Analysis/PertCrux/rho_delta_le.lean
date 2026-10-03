import Mathlib

namespace Work.Analysis.PertCrux

theorem rho_delta_le
    {ρ₁ δ Ξ' : ℝ} (hΞ' : 10 ≤ Ξ') (hδ : 0 < δ) (hρpos : 0 < ρ₁)
    (hρΞ : ρ₁ ≤ Ξ') (hδΞ : δ ≤ Ξ') :
    ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) ≤ 1 / (10 ^ 50 * Ξ' ^ 198) := by
  have hΞ'pos : 0 < Ξ' := by linarith
  have hnum : ρ₁ * δ ≤ Ξ' ^ 2 := by
    have h1 : ρ₁ * δ ≤ Ξ' * Ξ' :=
      mul_le_mul hρΞ hδΞ (le_of_lt hδ) (le_of_lt hΞ'pos)
    nlinarith [h1]
  have hpow : Ξ' ^ 200 ≤ (Ξ' ^ 2 + 1) ^ 100 := by
    have h2 : Ξ' ^ 2 ≤ Ξ' ^ 2 + 1 := by linarith [sq_nonneg Ξ']
    have h3 : (Ξ' ^ 2) ^ 100 ≤ (Ξ' ^ 2 + 1) ^ 100 :=
      pow_le_pow_left₀ (by positivity) h2 100
    have h4 : (Ξ' ^ 2) ^ 100 = Ξ' ^ 200 := by rw [← pow_mul]
    rwa [h4] at h3
  have hD : 0 < 10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100 := by positivity
  have hD2 : 0 < 10 ^ 50 * Ξ' ^ 198 := by positivity
  have hmain : Ξ' ^ 2 / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) ≤ 1 / (10 ^ 50 * Ξ' ^ 198) := by
    rw [div_le_div_iff₀ hD hD2]
    have he : Ξ' ^ 2 * (10 ^ 50 * Ξ' ^ 198) = 10 ^ 50 * Ξ' ^ 200 := by ring
    rw [he, one_mul]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  exact le_trans (div_le_div_of_nonneg_right hnum (le_of_lt hD)) hmain

end Work.Analysis.PertCrux
