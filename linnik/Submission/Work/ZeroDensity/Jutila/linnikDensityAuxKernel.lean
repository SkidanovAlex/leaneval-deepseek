import Mathlib

namespace Work.ZeroDensity.Jutila

/-- Auxiliary kernel bound used in the Jutila-type zero-density argument for Linnik's
theorem. For `l ∈ (0,1]`, a complex point `u` with `1 - l ≤ u.re ≤ 1` and `|u.im - T| ≤ l/2`
satisfies `1 / (5 l) ≤ (1 + l - u.re) / ((1 + l - u.re)^2 + (T - u.im)^2)`. -/
theorem linnikDensityAuxKernel {l T : ℝ} {u : ℂ} (hl0 : 0 < l) (hl1 : l ≤ 1)
    (hu1 : 1 - l ≤ u.re) (hu2 : u.re ≤ 1) (huim : |u.im - T| ≤ l / 2) :
    1 / (5 * l) ≤ (1 + l - u.re) / ((1 + l - u.re) ^ 2 + (T - u.im) ^ 2) := by
  have hxpos : 0 < 1 + l - u.re := by linarith
  have hden : 0 < (1 + l - u.re) ^ 2 + (T - u.im) ^ 2 := by nlinarith [sq_nonneg (T - u.im)]
  rw [le_div_iff₀ hden]
  have hy : (T - u.im) ^ 2 ≤ (l / 2) ^ 2 := by
    rw [sq_le_sq, abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < l / 2)]
    exact huim
  have hx2 : (1 + l - u.re) ≤ 2 * l := by linarith
  have hx1 : l ≤ 1 + l - u.re := by linarith
  have key : (1 + l - u.re) ^ 2 + (T - u.im) ^ 2 ≤ 5 * l * (1 + l - u.re) := by
    nlinarith [hy, hx1, hx2, hl0]
  have hpos : (0:ℝ) < 1 / (5 * l) := by positivity
  have hstep := mul_le_mul_of_nonneg_left key hpos.le
  have hsimp : 1 / (5 * l) * (5 * l * (1 + l - u.re)) = 1 + l - u.re := by
    field_simp
  linarith [hstep, hsimp.le, hsimp.ge]

end Work.ZeroDensity.Jutila
