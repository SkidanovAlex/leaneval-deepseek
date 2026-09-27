import Mathlib

namespace Work.EKLC6Core

/-- The counting constant for the entry-box cover: with `N = ⌈96/δ⌉ + 1` the `9`-fold grid
`(2N+1)^9` is bounded by `C (1 + δ⁻¹)^9` with `C` an absolute constant. -/
theorem entrybox_card_bound : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
    (((2 * (⌈(96 : ℝ) / δ⌉₊ + 1) + 1) ^ 9 : ℕ) : ℝ) ≤ C * (1 + δ⁻¹) ^ 9 := by
  refine ⟨(197:ℝ)^9, by positivity, ?_⟩
  intro δ hδ
  push_cast
  rw [div_eq_mul_inv]
  -- `⌈96·δ⁻¹⌉ ≤ 96·δ⁻¹ + 1`, hence the side length `2·(⌈96/δ⌉+1)+1` of the grid
  -- is at most `197·(1 + δ⁻¹)`.
  have hc : (⌈(96:ℝ) * δ⁻¹⌉₊ : ℝ) < 96 * δ⁻¹ + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hA : 2 * ((⌈(96:ℝ) * δ⁻¹⌉₊ : ℝ) + 1) + 1 ≤ 197 * (1 + δ⁻¹) := by
    have : (0:ℝ) ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    linarith
  have h9 := pow_le_pow_left₀
    (by positivity : (0:ℝ) ≤ 2 * ((⌈(96:ℝ) * δ⁻¹⌉₊ : ℝ) + 1) + 1) hA 9
  rw [mul_pow] at h9
  exact h9

end Work.EKLC6Core
