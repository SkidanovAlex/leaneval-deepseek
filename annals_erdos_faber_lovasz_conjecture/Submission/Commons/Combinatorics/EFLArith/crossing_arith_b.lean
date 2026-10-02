import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Combinatorics.EFLArith

theorem crossing_arith_b {ρ ε γ : ℝ} {n : ℕ} (hρ : 0 < ρ) (hγ : 0 < γ)
    (hγε : 1000 * γ ≤ ρ * ε) (hεs : 1000 * ε ≤ 1) :
    ρ * (n : ℝ) / 7 ≤ ρ * ((n : ℝ) / 6 - ε * n) - 11 * γ * n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hεle : ε ≤ 1 / 1000 := by linarith
  have hγle : γ ≤ ρ * ε / 1000 := by linarith
  have hkey : ρ * ε + 11 * γ ≤ ρ / 42 := by nlinarith [hγle, hεle, hρ]
  nlinarith [hkey, hn]

end Commons.Combinatorics.EFLArith