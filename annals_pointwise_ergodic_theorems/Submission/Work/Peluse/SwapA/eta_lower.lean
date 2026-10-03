import Mathlib

namespace Work.Peluse.SwapA

/-- The truncated density parameter `min 1 (Δ/(4C_G))` is bounded below by
`min 1 (B/(4C_G)) · γ^E` whenever `B γ^E ≤ Δ`, `0 < γ ≤ 1`. -/
theorem eta_lower {γ Δ B C_G : ℝ} {E : ℕ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hB0 : 0 < B) (hCG0 : 0 < C_G) (hΔ : B * γ ^ E ≤ Δ) :
    min 1 (B / (4 * C_G)) * γ ^ E ≤ min 1 (Δ / (4 * C_G)) := by
  have hγE0 : 0 ≤ γ ^ E := pow_nonneg hγ0.le E
  have hγE1 : γ ^ E ≤ 1 := pow_le_one₀ hγ0.le hγ1
  have hmin0 : 0 ≤ min 1 (B / (4 * C_G)) := le_min zero_le_one (by positivity)
  have hminB : min 1 (B / (4 * C_G)) ≤ B / (4 * C_G) := min_le_right _ _
  apply le_min
  · calc min 1 (B / (4 * C_G)) * γ ^ E ≤ min 1 (B / (4 * C_G)) * 1 :=
        mul_le_mul_of_nonneg_left hγE1 hmin0
      _ = min 1 (B / (4 * C_G)) := mul_one _
      _ ≤ 1 := min_le_left _ _
  · calc min 1 (B / (4 * C_G)) * γ ^ E ≤ (B / (4 * C_G)) * γ ^ E :=
        mul_le_mul_of_nonneg_right hminB hγE0
      _ = (B * γ ^ E) / (4 * C_G) := by ring
      _ ≤ Δ / (4 * C_G) := div_le_div_of_nonneg_right hΔ (by positivity)

end Work.Peluse.SwapA
