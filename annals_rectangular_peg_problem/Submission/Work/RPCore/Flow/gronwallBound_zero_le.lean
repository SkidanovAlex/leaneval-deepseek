import Mathlib

namespace Work.RPCore.Flow

/-- For `δ = 0`, `K ≥ 0`, `ε ≥ 0` and `t ≥ 0`, the Grönwall bound is at most
`ε * t * exp (K * t)`. Equivalently `(ε / K) * (exp (K * t) - 1) ≤ ε * t * exp (K * t)`.

The key estimate is `exp (K * t) - 1 ≤ (K * t) * exp (K * t)`, which follows from
`exp (-(K * t)) ≥ 1 - K * t`. -/
theorem gronwallBound_zero_le {K ε t : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    gronwallBound 0 K ε t ≤ ε * t * Real.exp (K * t) := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · subst hK0
    rw [gronwallBound_K0]
    simp
  · rw [gronwallBound_of_K_ne_0 (ne_of_gt hKpos)]
    simp only [zero_mul, zero_add]
    have hexp_pos : 0 < Real.exp (K * t) := Real.exp_pos _
    have key : 1 - Real.exp (-(K * t)) ≤ K * t := by
      have h := Real.add_one_le_exp (-(K * t)); linarith
    have hcore : Real.exp (K * t) - 1 ≤ (K * t) * Real.exp (K * t) := by
      have hmul := mul_le_mul_of_nonneg_right key (le_of_lt hexp_pos)
      rw [Real.exp_neg] at hmul
      have he : (1 - (Real.exp (K * t))⁻¹) * Real.exp (K * t) = Real.exp (K * t) - 1 := by
        rw [sub_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hexp_pos)]
      rwa [he] at hmul
    have hstep : ε / K * (Real.exp (K * t) - 1) ≤ ε / K * ((K * t) * Real.exp (K * t)) :=
      mul_le_mul_of_nonneg_left hcore (div_nonneg hε (le_of_lt hKpos))
    have hsimp : ε / K * ((K * t) * Real.exp (K * t)) = ε * t * Real.exp (K * t) := by
      field_simp
    linarith [hstep, hsimp]

end Work.RPCore.Flow
