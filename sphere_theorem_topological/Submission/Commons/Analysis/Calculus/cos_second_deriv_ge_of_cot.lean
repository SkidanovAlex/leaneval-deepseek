import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Commons.Analysis.Calculus

theorem cos_second_deriv_ge_of_cot {ρ ρ' ρ'' : ℝ → ℝ} {T : ℝ}
    (hπ : ∀ t ∈ Set.Ioo (0 : ℝ) T, ρ t ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hc : ∀ t ∈ Set.Ioo (0 : ℝ) T, ρ'' t ≤ Real.cot (ρ t) * (1 - ρ' t ^ 2)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      -(Real.cos (ρ t)) ≤ -(Real.sin (ρ t) * ρ'' t) - Real.cos (ρ t) * (ρ' t) ^ 2 := by
  intro t ht
  have hρ := hπ t ht
  have hsin_pos : 0 < Real.sin (ρ t) := Real.sin_pos_of_pos_of_lt_pi hρ.1 hρ.2
  have hsin_ne : Real.sin (ρ t) ≠ 0 := ne_of_gt hsin_pos
  have hcot := hc t ht
  rw [Real.cot_eq_cos_div_sin] at hcot
  have step : Real.sin (ρ t) * ρ'' t ≤ Real.cos (ρ t) * (1 - ρ' t ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hcot (le_of_lt hsin_pos)
    calc Real.sin (ρ t) * ρ'' t
        ≤ Real.sin (ρ t) * (Real.cos (ρ t) / Real.sin (ρ t) * (1 - ρ' t ^ 2)) := hmul
      _ = Real.cos (ρ t) * (1 - ρ' t ^ 2) := by
          rw [← mul_assoc, mul_div_cancel₀ (Real.cos (ρ t)) hsin_ne]
  have hgoal : Real.sin (ρ t) * ρ'' t + Real.cos (ρ t) * (ρ' t) ^ 2 ≤ Real.cos (ρ t) := by
    nlinarith [step]
  have h2 : -(Real.cos (ρ t)) ≤
      -(Real.sin (ρ t) * ρ'' t + Real.cos (ρ t) * (ρ' t) ^ 2) := neg_le_neg hgoal
  linarith [h2]

end Commons.Analysis.Calculus