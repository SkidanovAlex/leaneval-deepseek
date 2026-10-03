import Mathlib
import Submission.Work.Analysis.PertCrux.sqrt_delta0_le
import Submission.Work.Analysis.PertCrux.rho_delta_le

namespace Work.Analysis.PertCrux

theorem sqrt_two_delta0_bound {ρ₁ δ δ₀ Ξ' : ℝ}
    (hΞ' : 10 ≤ Ξ') (hδ : 0 < δ) (hρpos : 0 < ρ₁) (hρΞ : ρ₁ ≤ Ξ') (hδΞ : δ ≤ Ξ')
    (hδ₀tiny : δ₀ ≤ ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200)) :
    Real.sqrt (2 * δ₀) ≤ 2 / (10 ^ 50 * Ξ' ^ 198) := by
  have hsqrt2nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsplit : Real.sqrt (2 * δ₀) = Real.sqrt 2 * Real.sqrt δ₀ :=
    Real.sqrt_mul (by norm_num) δ₀
  rw [hsplit]
  have h2 : Real.sqrt δ₀ ≤ ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) :=
    sqrt_delta0_le hδ hρpos hδ₀tiny
  have h3 : Real.sqrt 2 * Real.sqrt δ₀ ≤
      Real.sqrt 2 * (ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100)) :=
    mul_le_mul_of_nonneg_left h2 hsqrt2nonneg
  have h4 : Real.sqrt 2 * (ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100)) ≤
      Real.sqrt 2 * (1 / (10 ^ 50 * Ξ' ^ 198)) :=
    mul_le_mul_of_nonneg_left (rho_delta_le hΞ' hδ hρpos hρΞ hδΞ) hsqrt2nonneg
  have h5 : Real.sqrt 2 * (1 / (10 ^ 50 * Ξ' ^ 198)) ≤ 2 / (10 ^ 50 * Ξ' ^ 198) := by
    have hle : Real.sqrt 2 ≤ 2 := by
      rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right hle (by positivity)
  linarith [h3, h4, h5]

end Work.Analysis.PertCrux
