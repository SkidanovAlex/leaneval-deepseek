import Mathlib
import Submission.Work.Analysis.PertCrux.sqrt_delta0_le
import Submission.Work.Analysis.PertCrux.rho_delta_le

namespace Work.Analysis.PertCrux

/-- Arithmetic chaser for the perturbative estimates: from `δ₀ ≤ ρ₁^2 δ^2 / (10^100 (Ξ'^2+1)^200)`
and the two crude bounds `‖α‖ ≤ 2√(2δ₀)`, `‖u₀ - 1‖ ≤ 4δ₀/ρ₁^2 + M₀√(2δ₀)` one obtains the
explicitly scaled estimates used downstream. -/
theorem bounds_pert
    {δ₀ ρ₁ δ Ξ' M₀ : ℝ} {u₀ α : ℂ}
    (hΞ' : 10 ≤ Ξ') (hδ : 0 < δ) (hρpos : 0 < ρ₁) (hρΞ : ρ₁ ≤ Ξ') (hδΞ : δ ≤ Ξ')
    (hM₀ : 0 ≤ M₀) (hM₀Ξ : M₀ ≤ Ξ')
    (hδ₀tiny : δ₀ ≤ ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200))
    (hu1 : ‖u₀ - 1‖ ≤ 4 * δ₀ / ρ₁ ^ 2 + M₀ * Real.sqrt (2 * δ₀))
    (hαle : ‖α‖ ≤ 2 * Real.sqrt (2 * δ₀)) :
    ‖α‖ ≤ 2 * Real.sqrt 2 * ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) ∧
    ‖α‖ ≤ 2 * Real.sqrt 2 / (10 ^ 50 * Ξ' ^ 198) ∧
    ‖u₀ - 1‖ ≤ 4 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200)
      + Real.sqrt 2 * Ξ' * ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) := by
  -- the square-root consequence of the tininess hypothesis on `δ₀`
  have hsqrtδ₀ : Real.sqrt δ₀ ≤ ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) :=
    sqrt_delta0_le hδ hρpos hδ₀tiny
  -- first conjunct
  have hg1 : ‖α‖ ≤ 2 * Real.sqrt 2 * ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) := by
    have h2 : Real.sqrt (2 * δ₀) = Real.sqrt 2 * Real.sqrt δ₀ := Real.sqrt_mul (by norm_num) δ₀
    calc ‖α‖ ≤ 2 * Real.sqrt (2 * δ₀) := hαle
      _ = 2 * (Real.sqrt 2 * Real.sqrt δ₀) := by rw [h2]
      _ ≤ 2 * (Real.sqrt 2 * (ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsqrtδ₀ (Real.sqrt_nonneg 2)) (by norm_num)
      _ = 2 * Real.sqrt 2 * ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) := by ring
  -- second conjunct
  have hg2 : ‖α‖ ≤ 2 * Real.sqrt 2 / (10 ^ 50 * Ξ' ^ 198) := by
    refine le_trans hg1 ?_
    have hr := rho_delta_le hΞ' hδ hρpos hρΞ hδΞ
    calc 2 * Real.sqrt 2 * ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100)
        = 2 * Real.sqrt 2 * (ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100)) := by ring
      _ ≤ 2 * Real.sqrt 2 * (1 / (10 ^ 50 * Ξ' ^ 198)) :=
            mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 2 * Real.sqrt 2 / (10 ^ 50 * Ξ' ^ 198) := by ring
  -- third conjunct
  have hg3 : ‖u₀ - 1‖ ≤ 4 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200)
      + Real.sqrt 2 * Ξ' * ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) := by
    -- the `4 δ₀ / ρ₁^2` term
    have h4 : 4 * δ₀ / ρ₁ ^ 2 ≤ 4 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200) := by
      have hp2 : (0:ℝ) < ρ₁ ^ 2 := by positivity
      have h4' : 4 * δ₀ ≤ 4 * (ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200)) := by
        linarith
      have h := div_le_div_of_nonneg_right h4' (le_of_lt hp2)
      have heq : 4 * (ρ₁ ^ 2 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200)) / ρ₁ ^ 2
          = 4 * δ ^ 2 / (10 ^ 100 * (Ξ' ^ 2 + 1) ^ 200) := by
        field_simp
      rwa [heq] at h
    -- the `M₀ √(2 δ₀)` term
    have h5 : M₀ * Real.sqrt (2 * δ₀)
        ≤ Real.sqrt 2 * Ξ' * ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) := by
      have h2 : Real.sqrt (2 * δ₀) = Real.sqrt 2 * Real.sqrt δ₀ := Real.sqrt_mul (by norm_num) δ₀
      calc M₀ * Real.sqrt (2 * δ₀) = M₀ * (Real.sqrt 2 * Real.sqrt δ₀) := by rw [h2]
        _ ≤ M₀ * (Real.sqrt 2 * (ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsqrtδ₀ (Real.sqrt_nonneg 2)) hM₀
        _ ≤ Ξ' * (Real.sqrt 2 * (ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100))) :=
              mul_le_mul_of_nonneg_right hM₀Ξ (by positivity)
        _ = Real.sqrt 2 * Ξ' * ρ₁ * δ / (10 ^ 50 * (Ξ' ^ 2 + 1) ^ 100) := by ring
    exact le_trans hu1 (add_le_add h4 h5)
  exact ⟨hg1, hg2, hg3⟩

end Work.Analysis.PertCrux
