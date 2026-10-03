import Mathlib

namespace Work.Pert

theorem SmallDataArith {ρ δ₀ η rr : ℝ} {c0 c1 : ℝ}
    (hρ : 0 < ρ) (hρ100 : ρ ≤ 1 / 100) (hδ : 0 < δ₀) (hη : 0 < η) (hrr : 0 < rr)
    (hX : 65536 * δ₀ ≤ ρ ^ 2) (hZ : 262144 * η * δ₀ ≤ ρ)
    (hrrge : 1 / (4 * η) ≤ rr)
    (hu : c0 ≤ 10 * (δ₀ / ρ ^ 2 + δ₀ / (ρ * rr)))
    (hα : c1 ≤ 10 * δ₀ / ρ) :
    c0 ≤ 1 / 1024 ∧ 2 * Real.pi * c1 * η ≤ 1 / 64 ∧ c1 ≤ 1 / 1024 ∧ c1 * η ≤ 1 / 1024 := by
  have hρ2pos : (0:ℝ) < ρ ^ 2 := by positivity
  have h4η : (0:ℝ) < 4 * η := by positivity
  -- bound on δ₀/ρ² coming from 65536 δ₀ ≤ ρ²
  have hA : δ₀ / ρ ^ 2 ≤ 1 / 65536 := by
    rw [div_le_iff₀ hρ2pos]; nlinarith [hX]
  -- 1/rr ≤ 4η from rr ≥ 1/(4η)
  have hInvrr : 1 / rr ≤ 4 * η := by
    rw [div_le_iff₀ hrr]
    have h := (div_le_iff₀ h4η).mp hrrge
    nlinarith [h]
  -- bound on δ₀/(ρ*rr)
  have hB : δ₀ / (ρ * rr) ≤ 1 / 65536 := by
    have hstep : δ₀ / (ρ * rr) ≤ 4 * η * δ₀ / ρ :=
      calc δ₀ / (ρ * rr) = (δ₀ / ρ) * (1 / rr) := by ring
        _ ≤ (δ₀ / ρ) * (4 * η) := mul_le_mul_of_nonneg_left hInvrr (by positivity)
        _ = 4 * η * δ₀ / ρ := by ring
    have h4 : 4 * η * δ₀ / ρ ≤ 1 / 65536 := by
      rw [div_le_iff₀ hρ]; nlinarith [hZ]
    linarith [hstep, h4]
  -- the c0 bound
  have hM0 : 10 * (δ₀ / ρ ^ 2 + δ₀ / (ρ * rr)) ≤ 1 / 1024 := by
    nlinarith [hA, hB]
  have hc0 : c0 ≤ 1 / 1024 := le_trans hu hM0
  -- the bounds on c1
  have hC : 10 * δ₀ / ρ ≤ 1 / 1024 := by
    rw [div_le_iff₀ hρ]; nlinarith [hX, hρ100, hρ]
  have hc1le : c1 ≤ 1 / 1024 := le_trans hα hC
  have hM1η : 10 * δ₀ / ρ * η ≤ 1 / 1024 := by
    have heq : 10 * δ₀ / ρ * η = 10 * η * δ₀ / ρ := by ring
    rw [heq, div_le_iff₀ hρ]; nlinarith [hZ]
  have hc1η : c1 * η ≤ 1 / 1024 :=
    le_trans (mul_le_mul_of_nonneg_right hα (le_of_lt hη)) hM1η
  have hED : η * δ₀ / ρ ≤ 1 / 262144 := by
    rw [div_le_iff₀ hρ]; nlinarith [hZ]
  have hM1πη : 2 * Real.pi * (10 * δ₀ / ρ) * η ≤ 1 / 64 := by
    have heq : 2 * Real.pi * (10 * δ₀ / ρ) * η = 20 * Real.pi * (η * δ₀ / ρ) := by ring
    rw [heq]
    have hb : 20 * Real.pi * (η * δ₀ / ρ) ≤ 20 * Real.pi * (1 / 262144) :=
      mul_le_mul_of_nonneg_left hED (by positivity)
    have h2 : 20 * Real.pi * (1 / 262144) ≤ 1 / 64 := by nlinarith [Real.pi_lt_four]
    linarith [hb, h2]
  have hc1πη : 2 * Real.pi * c1 * η ≤ 1 / 64 := by
    have hcoef : 0 ≤ 2 * Real.pi * η := by positivity
    have hstep : 2 * Real.pi * c1 * η ≤ 2 * Real.pi * (10 * δ₀ / ρ) * η := by
      have h1 : 2 * Real.pi * c1 * η = (2 * Real.pi * η) * c1 := by ring
      have h2 : 2 * Real.pi * (10 * δ₀ / ρ) * η = (2 * Real.pi * η) * (10 * δ₀ / ρ) := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left hα hcoef
    linarith [hstep, hM1πη]
  exact ⟨hc0, hc1πη, hc1le, hc1η⟩

end Work.Pert
