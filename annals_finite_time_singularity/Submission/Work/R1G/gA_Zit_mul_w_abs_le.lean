import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.R1G.AnG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- Elementary bound: for `z ≥ 0`, `(1+z)^4 ≤ 4 (1+z²)^4`.
Indeed `(1+z)^2 ≤ 2(1+z²)` (AM–GM) and `(1+z²)^2 ≤ (1+z²)^4`. -/
theorem one_add_pow_four_le (z : ℝ) (hz : 0 ≤ z) : (1 + z) ^ 4 ≤ 4 * (1 + z ^ 2) ^ 4 := by
  have hb : (1 : ℝ) ≤ 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  have h1 : (1 + z) ^ 2 ≤ 2 * (1 + z ^ 2) := by nlinarith [sq_nonneg (1 - z)]
  have hub : (1 + z ^ 2) ^ 2 ≤ (1 + z ^ 2) ^ 4 :=
    pow_le_pow_right₀ hb (by norm_num : (2 : ℕ) ≤ 4)
  have h2 : ((1 + z) ^ 2) ^ 2 ≤ (2 * (1 + z ^ 2)) ^ 2 := by
    apply sq_le_sq' <;> nlinarith [h1, sq_nonneg z]
  have h3 : (2 * (1 + z ^ 2)) ^ 2 = 4 * (1 + z ^ 2) ^ 2 := by ring
  calc (1 + z) ^ 4 = ((1 + z) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (1 + z ^ 2)) ^ 2 := h2
    _ = 4 * (1 + z ^ 2) ^ 2 := h3
    _ ≤ 4 * (1 + z ^ 2) ^ 4 := by linarith [hub]

/-- The uniform radial bound for the first three `D_z`-iterates:
`|Zit j z| ≤ 36 · z²/(1+z²)⁴` for `j < 3` and `z ≥ 0`.
This is exactly the factor that cancels the `z²` in the weight `w z = (1+z)²/z²`. -/
theorem Zit_abs_le (j : ℕ) (hj : j < 3) {z : ℝ} (hz : 0 ≤ z) :
    |Zit j z| ≤ 36 * z ^ 2 / (1 + z ^ 2) ^ 4 := by
  interval_cases j
  · rw [Zit_zero]
    have h := Zf_nonneg hz
    calc |Zf z| = Zf z := abs_of_nonneg h
      _ ≤ 36 * Zf z := by nlinarith [h]
      _ = 36 * z ^ 2 / (1 + z ^ 2) ^ 4 := by rw [Zf]; ring
  · rw [Zit_one]
    rw [Zf1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + z ^ 2) ^ 5)]
    have hn : |2 * z ^ 2 - 6 * z ^ 4| ≤ 36 * z ^ 2 * (1 + z ^ 2) := by
      rw [show 2 * z ^ 2 - 6 * z ^ 4 = z ^ 2 * (2 - 6 * z ^ 2) by ring, abs_mul,
        abs_of_nonneg (sq_nonneg z)]
      have h : |2 - 6 * z ^ 2| ≤ 36 * (1 + z ^ 2) := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg z]
      nlinarith [sq_nonneg z]
    have hn2 := mul_le_mul_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ (1 + z ^ 2) ^ 4)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [show (1 + z ^ 2) ^ 5 = (1 + z ^ 2) ^ 4 * (1 + z ^ 2) by ring]
    linarith [hn2]
  · rw [Zit_two]
    rw [Zf2, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + z ^ 2) ^ 6)]
    have hn : |4 * z ^ 2 - 40 * z ^ 4 + 36 * z ^ 6| ≤ 36 * z ^ 2 * (1 + z ^ 2) ^ 2 := by
      rw [show 4 * z ^ 2 - 40 * z ^ 4 + 36 * z ^ 6 = z ^ 2 * (4 - 40 * z ^ 2 + 36 * z ^ 4) by ring,
        abs_mul, abs_of_nonneg (sq_nonneg z)]
      have h : |4 - 40 * z ^ 2 + 36 * z ^ 4| ≤ 36 * (1 + z ^ 2) ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg z]
      nlinarith [sq_nonneg z]
    have hn2 := mul_le_mul_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ (1 + z ^ 2) ^ 4)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [show (1 + z ^ 2) ^ 6 = (1 + z ^ 2) ^ 4 * (1 + z ^ 2) ^ 2 by ring]
    linarith [hn2]

theorem gA_Zit_mul_w_abs_le (j : ℕ) (hj : j < 3) {z : ℝ} (hz : 0 ≤ z) :
    |Work.R1G.Zit j z * Work.Spaces.w z| ≤ 144 / (1 + z) ^ 2 := by
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · rw [← hz0]
    have hw : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw, mul_zero, abs_zero]
    norm_num
  · rw [abs_mul, Work.Spaces.w]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) ^ 2 / z ^ 2)]
    have hb : |Zit j z| ≤ 36 * z ^ 2 / (1 + z ^ 2) ^ 4 := Zit_abs_le j hj (le_of_lt hzpos)
    calc |Zit j z| * ((1 + z) ^ 2 / z ^ 2)
        ≤ (36 * z ^ 2 / (1 + z ^ 2) ^ 4) * ((1 + z) ^ 2 / z ^ 2) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 36 * (1 + z) ^ 2 / (1 + z ^ 2) ^ 4 := by
          rw [div_mul_div_comm]
          rw [show 36 * z ^ 2 * (1 + z) ^ 2 = 36 * (1 + z) ^ 2 * z ^ 2 by ring]
          rw [mul_div_mul_right (36 * (1 + z) ^ 2) ((1 + z ^ 2) ^ 4) (by positivity : z ^ 2 ≠ 0)]
      _ ≤ 144 / (1 + z) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h : (1 + z) ^ 4 ≤ 4 * (1 + z ^ 2) ^ 4 := one_add_pow_four_le z (le_of_lt hzpos)
          nlinarith [h]

end Work.R1G
