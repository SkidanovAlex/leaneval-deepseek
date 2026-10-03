import Mathlib

namespace Work.Analysis.PertCrux

/-- If `δ₀` is at most `ρ₁^2 δ^2 / (10^100 * (Ξ'^2 + 1)^200)`, then its square root is at
most `ρ₁ δ / (10^50 * (Ξ'^2 + 1)^100)`. -/
theorem sqrt_delta0_le
    {ρ₁ δ δ₀ Ξ' : ℝ}
    (hδ : 0 < δ) (hρpos : 0 < ρ₁)
    (hδ₀tiny : δ₀ ≤ ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200)) :
    Real.sqrt δ₀ ≤ ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) := by
  have h1 : Real.sqrt δ₀ ≤
      Real.sqrt (ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200)) :=
    Real.sqrt_le_sqrt hδ₀tiny
  have hs100 : Real.sqrt ((10 : ℝ) ^ 100) = 10 ^ 50 := by
    rw [show (10 : ℝ) ^ 100 = ((10 : ℝ) ^ 50) ^ 2 from by rw [← pow_mul]]
    exact Real.sqrt_sq (by positivity)
  have hsX : Real.sqrt ((Ξ' ^ 2 + 1) ^ 200) = (Ξ' ^ 2 + 1) ^ 100 := by
    rw [show (Ξ' ^ 2 + 1) ^ 200 = ((Ξ' ^ 2 + 1) ^ 100) ^ 2 from by rw [← pow_mul]]
    exact Real.sqrt_sq (by positivity)
  have h2 : Real.sqrt (ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200))
      = ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) := by
    rw [Real.sqrt_div (by positivity)]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_sq (le_of_lt hρpos), Real.sqrt_sq (le_of_lt hδ)]
    rw [hs100, hsX]
  rw [h2] at h1
  exact h1

end Work.Analysis.PertCrux
