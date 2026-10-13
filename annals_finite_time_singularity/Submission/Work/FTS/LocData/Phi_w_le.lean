/-
# `Work.FTS.LocData.Phi_w_le`

The weighted bound `|w(z) · Phi i z θ| ≤ 2/z` for `z ≥ 1` and `i ≤ 4`, where
`w z = (1+z)²/z²` and `Phi i z θ = PhiR i z / (1+z)^{i+2}`.

Since `PhiR i z = 2z·R_i(z)` with `R_0 = 1`, `R_1 = 1-z`, `R_2 = 1-4z+z²`,
`R_3 = 1-11z+11z²-z³`, `R_4 = 1-26z+66z²-26z³+z⁴`, the whole content is the
polynomial inequality `|R_i z| ≤ (1+z)^i` for `z ≥ 1` (`i ≤ 4`), proved here by
elementary algebraic estimates (`nlinarith` with explicit sum-of-squares hints;
for `i = 4` the palindromic quartic is handled via
`z⁴-11z³+36z²-11z+1 = (z² - (11/2)z + 1)² + (15/4)z²`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.LocData.HkFstarDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- **Conversion step.**  A bound `|PhiR i z| ≤ 2z(1+z)^i` for `z ≥ 1` gives the weighted
bound `|w z · Phi i z θ| ≤ 2/z`: indeed `w z · Phi i z θ = PhiR i z /(z²(1+z)^i)` and the
denominator is positive. -/
theorem Phi_w_le_of_abs_PhiR (i : ℕ) {z : ℝ} (hz1 : 1 ≤ z) (θ : ℝ)
    (h : |PhiR i z| ≤ 2 * z * (1 + z) ^ i) :
    |Work.Spaces.w z * Phi i z θ| ≤ 2 / z := by
  have hz : 0 < z := lt_of_lt_of_le one_pos hz1
  have hden : 0 < z ^ 2 * (1 + z) ^ i := by positivity
  have hkey : Work.Spaces.w z * Phi i z θ = PhiR i z / (z ^ 2 * (1 + z) ^ i) := by
    simp only [Work.Spaces.w, Phi]
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have h2 : 2 / z * (z ^ 2 * (1 + z) ^ i) = 2 * z * (1 + z) ^ i := by field_simp
  rw [h2]
  exact h

theorem Phi_w_le (i : ℕ) (hi : i ≤ 4) {z : ℝ} (hz1 : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.w z * Phi i z θ| ≤ 2 / z := by
  refine Phi_w_le_of_abs_PhiR i hz1 θ ?_
  interval_cases i
  · simp only [PhiR_zero, pow_zero, mul_one]
    rw [abs_of_pos (by linarith : (0 : ℝ) < 2 * z)]
  · simp only [PhiR_one, pow_one]
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * z),
      abs_of_nonpos (by linarith : 1 - z ≤ 0)]
    nlinarith [hz1]
  · simp only [PhiR_two]
    have habs : |1 - 4 * z + z ^ 2| ≤ (1 + z) ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (z - 1 / 2), hz1]
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * z)]
    exact mul_le_mul_of_nonneg_left habs (by linarith : (0 : ℝ) ≤ 2 * z)
  · simp only [PhiR_three]
    have habs : |1 - 11 * z + 11 * z ^ 2 - z ^ 3| ≤ (1 + z) ^ 3 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (z - 2), sq_nonneg (z - 2 / 7), hz1]
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * z)]
    exact mul_le_mul_of_nonneg_left habs (by linarith : (0 : ℝ) ≤ 2 * z)
  · simp only [PhiR_four]
    have habs : |1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4| ≤ (1 + z) ^ 4 := by
      rw [abs_le]
      constructor <;>
        nlinarith [sq_nonneg (z - 1), sq_nonneg (z ^ 2 - 11 / 2 * z + 1), sq_nonneg z, hz1]
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * z)]
    exact mul_le_mul_of_nonneg_left habs (by linarith : (0 : ℝ) ≤ 2 * z)

end Work.FTS.LocData
