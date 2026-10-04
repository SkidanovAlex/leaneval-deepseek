import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

/-- **The numerical contradiction of the scalar-curvature spreading argument.**

If `S₀ ≥ 1`, `ε > 0`, `c₀ > 0`, `β ≤ β₀ ≤ ε√c₀/(4√2 π)`, and a length `r` satisfies both
`ε S₀ ≤ β (S₀√S₀ + S₀) r` (the drop of `S` along a minimising geodesic) and
`r ≤ π/√(c₀S₀/2)` (Bonnet–Myers with curvature `≥ c₀S₀`), then we get a contradiction.

Indeed, combining: `ε S₀ √(c₀S₀/2) ≤ β₀ π (S₀√S₀ + S₀)`.  Writing `x = √S₀ ≥ 1` and using
`β₀π = ε√c₀/(4√2)`, `√(c₀S₀/2) = x√(c₀/2)`, this is
`ε x³ √c₀/√2 ≤ ε √c₀ x²(x+1)/(4√2)`, i.e. `4x ≤ x+1` after cancelling the positive factor
`ε√c₀ x²/√2`; but `x ≥ 1` gives `4x ≥ 4 > x+1`.  Contradiction. -/
theorem spread_numeric {c₀ ε S₀ β β₀ r : ℝ}
    (hc₀ : 0 < c₀) (hε : 0 < ε) (hS₀ : 1 ≤ S₀)
    (hβ : 0 < β) (hββ₀ : β ≤ β₀)
    (hβ₀ : β₀ ≤ ε * Real.sqrt c₀ / (4 * Real.sqrt 2 * Real.pi))
    (hr : ε * S₀ ≤ β * (S₀ * Real.sqrt S₀ + S₀) * r)
    (hr' : r ≤ Real.pi / Real.sqrt (c₀ * S₀ / 2)) : False := by
  have hS₀pos : 0 < S₀ := lt_of_lt_of_le zero_lt_one hS₀
  have hsS₀pos : 0 < Real.sqrt S₀ := Real.sqrt_pos.mpr hS₀pos
  have hTpos : 0 < S₀ * Real.sqrt S₀ + S₀ := by nlinarith [mul_pos hS₀pos hsS₀pos]
  have hDpos : 0 < Real.sqrt (c₀ * S₀ / 2) := Real.sqrt_pos.mpr (by positivity)
  -- clear the denominator `√(c₀S₀/2)` in Bonnet–Myers
  have hrD : r * Real.sqrt (c₀ * S₀ / 2) ≤ Real.pi := (le_div_iff₀ hDpos).mp hr'
  -- multiply the drop inequality by `√(c₀S₀/2)` and combine with Bonnet–Myers
  have h4 : ε * S₀ * Real.sqrt (c₀ * S₀ / 2) ≤ β * (S₀ * Real.sqrt S₀ + S₀) * Real.pi := by
    have h1 := mul_le_mul_of_nonneg_right hr hDpos.le
    have h2 := mul_le_mul_of_nonneg_left hrD (le_of_lt (mul_pos hβ hTpos))
    linarith
  -- bound `βπ` by `ε√c₀/(4√2)`
  have hβπ : β * Real.pi ≤ ε * Real.sqrt c₀ / (4 * Real.sqrt 2) := by
    have hA : β * Real.pi ≤ β₀ * Real.pi := mul_le_mul_of_nonneg_right hββ₀ Real.pi_pos.le
    have hB : β₀ * Real.pi ≤ ε * Real.sqrt c₀ / (4 * Real.sqrt 2) := by
      have h := mul_le_mul_of_nonneg_right hβ₀ Real.pi_pos.le
      have heq : (ε * Real.sqrt c₀ / (4 * Real.sqrt 2 * Real.pi)) * Real.pi
          = ε * Real.sqrt c₀ / (4 * Real.sqrt 2) := by
        field_simp
      linarith
    linarith
  have h5 : ε * S₀ * Real.sqrt (c₀ * S₀ / 2)
      ≤ ε * Real.sqrt c₀ / (4 * Real.sqrt 2) * (S₀ * Real.sqrt S₀ + S₀) := by
    have h := mul_le_mul_of_nonneg_right hβπ hTpos.le
    linarith
  -- `√(c₀S₀/2) = √c₀ · √S₀ / √2`
  have hD_eq : Real.sqrt (c₀ * S₀ / 2) = Real.sqrt c₀ * Real.sqrt S₀ / Real.sqrt 2 := by
    rw [show c₀ * S₀ / 2 = c₀ * (S₀ / 2) by ring, Real.sqrt_mul hc₀.le,
      Real.sqrt_div (le_of_lt hS₀pos) 2]
    ring
  have h6 := mul_le_mul_of_nonneg_right h5 (by positivity : (0:ℝ) ≤ 4 * Real.sqrt 2)
  have hL : ε * S₀ * Real.sqrt (c₀ * S₀ / 2) * (4 * Real.sqrt 2)
      = ε * Real.sqrt c₀ * (4 * S₀ * Real.sqrt S₀) := by
    rw [hD_eq]
    field_simp
  have hR : (ε * Real.sqrt c₀ / (4 * Real.sqrt 2) * (S₀ * Real.sqrt S₀ + S₀)) * (4 * Real.sqrt 2)
      = ε * Real.sqrt c₀ * (S₀ * Real.sqrt S₀ + S₀) := by
    field_simp
  have h7 : ε * Real.sqrt c₀ * (4 * S₀ * Real.sqrt S₀)
      ≤ ε * Real.sqrt c₀ * (S₀ * Real.sqrt S₀ + S₀) := by
    rw [← hL, ← hR]
    exact h6
  -- cancel the positive factor `ε√c₀`
  have hεc : 0 < ε * Real.sqrt c₀ := mul_pos hε (Real.sqrt_pos.mpr hc₀)
  have h8 : 4 * S₀ * Real.sqrt S₀ ≤ S₀ * Real.sqrt S₀ + S₀ :=
    (mul_le_mul_iff_of_pos_left hεc).mp h7
  have h9 : 4 * Real.sqrt S₀ ≤ Real.sqrt S₀ + 1 := by
    have h' : S₀ * (4 * Real.sqrt S₀) ≤ S₀ * (Real.sqrt S₀ + 1) := by linarith
    exact (mul_le_mul_iff_of_pos_left hS₀pos).mp h'
  have h11 : 1 ≤ Real.sqrt S₀ := Real.one_le_sqrt.mpr hS₀
  linarith

end Work.Diff.L
