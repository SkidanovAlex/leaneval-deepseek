import Mathlib

namespace Work.Pert

theorem vtilde_alg {σ u0 uτ τ : ℂ} (hh : 1 + τ * uτ ≠ 0) (hE0 : 1 - σ * u0 ≠ 0) :
    (1 - σ * uτ / (1 + τ * uτ)) / (1 - σ * u0) - 1
      = σ * (τ * uτ * u0 - (uτ - u0)) / ((1 - σ * u0) * (1 + τ * uτ)) := by
  have hh' : 1 + uτ * τ ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

end Work.Pert
