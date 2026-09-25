import Mathlib

namespace Work.BourgainPlan.Maximal

theorem theta_mul_eq {q p p₀ θ : ℝ} (hq : 1 ≤ q) (hqp : q < p) (hpp : p < p₀)
    (hθ : p⁻¹ = θ * q⁻¹ + (1 - θ) * p₀⁻¹) :
    θ * p = q * (p₀ - p) / (p₀ - q) ∧ (1 - θ) * p = p₀ * (p - q) / (p₀ - q) := by
  have hp : p ≠ 0 := by linarith
  have hp₀ : p₀ ≠ 0 := by linarith
  have hq0 : q ≠ 0 := by linarith
  have hpq : p₀ - q ≠ 0 := by linarith
  have hkey : θ * p * (p₀ - q) = q * (p₀ - p) := by
    field_simp at hθ ⊢
    nlinarith [hθ]
  constructor
  · rw [eq_div_iff hpq]; linarith [hkey]
  · rw [eq_div_iff hpq]; nlinarith [hkey]

end Work.BourgainPlan.Maximal
