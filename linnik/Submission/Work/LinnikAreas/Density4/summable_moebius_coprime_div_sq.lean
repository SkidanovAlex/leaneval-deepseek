import Mathlib
import Submission.Work.LinnikAreas.Density4.SqfreeCoprimeDefs

namespace Work.LinnikAreas.Density4

/-- The Möbius series `∑_{m ⊥ r} μ(m)/m²` converges absolutely: termwise,
`|μ(m)/m²| ≤ 1/m²`, and `∑ 1/m² = π²/6` converges. -/
theorem summable_moebius_coprime_div_sq (r : ℕ) :
    Summable (fun m : ℕ =>
      if Nat.Coprime m r then (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ 2 else 0) := by
  -- Absolute convergence: dominate by `1/m²`, whose series converges.
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _ hasSum_zeta_two.summable
  intro m
  split_ifs with h
  · rw [norm_div]
    have hden : ‖((m : ℝ)) ^ 2‖ = (m : ℝ) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hden]
    have hμ : ‖(ArithmeticFunction.moebius m : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
    exact div_le_div_of_nonneg_right hμ (sq_nonneg _)
  · simp

end Work.LinnikAreas.Density4
