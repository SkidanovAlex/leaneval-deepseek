import Mathlib

namespace Work.KMTPlan.A6

/-- Interpolation data for the `L^r` estimate, `2 ≤ r < 2d/(d-1)`:

there is an intermediate exponent `q` with `r < q < 2d/(d-1)` and a weight `θ ∈ (0,1]` such that
`1/r = θ/1 + (1-θ)/q`, i.e. `1/r` is the affine combination of the endpoints `1/1 = 1` and `1/q`.

This is the elementary convexity step feeding the log-convexity interpolation of the bilinear
maximal/variational estimates (`≤ 2d/(d-1)` is the paper's (avg-1) range and `q = 1` is the sharp
`L¹` endpoint). -/
theorem exists_interp_theta {d r : ℝ} (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hrd : r < 2 * d / (d - 1)) :
    ∃ q θ : ℝ, r < q ∧ q < 2 * d / (d - 1) ∧ 1 < q ∧ 0 < θ ∧ θ ≤ 1 ∧
      1 / r = θ / 1 + (1 - θ) / q := by
  have hr0 : 0 < r := by linarith
  -- The intermediate exponent is the midpoint of `r` and the right end `2d/(d-1)`.
  set q : ℝ := (r + 2 * d / (d - 1)) / 2 with hq
  have hrq : r < q := by rw [hq]; linarith
  have hqM : q < 2 * d / (d - 1) := by rw [hq]; linarith
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  -- The interpolation weight, uniquely determined by the identity `1/r = θ·1 + (1-θ)/q`.
  set θ : ℝ := (1 / r - 1 / q) / (1 - 1 / q) with hθ
  have hden_pos : 0 < 1 - 1 / q := by
    have hlt : 1 / q < 1 := by
      rw [div_lt_one hq0]
      exact hq1
    linarith
  have hden_ne : 1 - 1 / q ≠ 0 := ne_of_gt hden_pos
  have hnum_pos : 0 < 1 / r - 1 / q := by
    have hlt : 1 / q < 1 / r := one_div_lt_one_div_of_lt hr0 hrq
    linarith
  -- The defining relation of `θ`, with the denominator cancelled.
  have hkey : θ * (1 - 1 / q) = 1 / r - 1 / q := by
    rw [hθ, div_mul_eq_mul_div, mul_div_cancel_right₀ _ hden_ne]
  refine ⟨q, θ, hrq, hqM, hq1, ?_, ?_, ?_⟩
  · rw [hθ]; exact div_pos hnum_pos hden_pos
  · rw [hθ, div_le_one hden_pos]
    have hle : 1 / r ≤ 1 := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num)
        (le_trans (by norm_num : (1 : ℝ) ≤ 2) hr)
      simpa using h
    linarith
  · rw [div_one]
    have hrhs : θ + (1 - θ) / q = θ * (1 - 1 / q) + 1 / q := by
      field_simp
      ring
    rw [hrhs, hkey]
    ring

end Work.KMTPlan.A6
