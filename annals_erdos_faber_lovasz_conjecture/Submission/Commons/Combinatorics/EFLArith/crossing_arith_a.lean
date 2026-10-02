import Mathlib.Algebra.Order.Star.Real

namespace Commons.Combinatorics.EFLArith

theorem crossing_arith_a {ρ ε γ : ℝ} {n : ℕ} (hρ : 0 < ρ) (hγ : 0 < γ)
    (hγε : 1000 * γ ≤ ρ * ε) (hεs : 1000 * ε ≤ 1) :
    ρ * (n : ℝ) / 7 ≤ ρ * ((49 : ℝ) / 50 - ε) * n - 12 * γ * n := by
  have hkey : ρ / 7 ≤ ρ * ((49 : ℝ) / 50 - ε) - 12 * γ := by
    nlinarith [hρ, hγ, hγε, hεs]
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h3 : 0 ≤ (ρ * ((49 : ℝ) / 50 - ε) - 12 * γ - ρ / 7) * (n:ℝ) :=
    mul_nonneg (by linarith) hn
  nlinarith [h3]

end Commons.Combinatorics.EFLArith