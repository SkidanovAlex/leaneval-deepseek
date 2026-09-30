import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Elementary trigonometric bound: for real `x`, `|2 sin(x/2)| ≤ |x|`,
which is the real form of `‖exp (I x) - 1‖ ≤ |x|`. -/
lemma abs_two_mul_sin_half_le (x : ℝ) : |(2 : ℝ) * Real.sin (x / 2)| ≤ |x| := by
  rw [abs_mul]
  have hx2 : |(2 : ℝ)| = 2 := by norm_num
  rw [hx2]
  have h : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  rw [abs_div, hx2] at h
  linarith

theorem norm_cpow_I_sub_one_le (t s : ℝ) (hs : 1 ≤ s) :
    ‖((s:ℝ):ℂ)^(Complex.I*(t:ℂ)) - 1‖ ≤ |t| * (s - 1) := by
  have hs0 : (0:ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hsne : ((s:ℝ):ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs0
  -- `s ^ (I t) = exp (log s * I t) = exp (I * (t * log s))`
  rw [Complex.cpow_def_of_ne_zero hsne, ← Complex.ofReal_log hs0.le]
  have harg : (↑(Real.log s) : ℂ) * (Complex.I * ↑t) = Complex.I * ↑(Real.log s * t) := by
    rw [Complex.ofReal_mul]; ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  -- now bound `|2 sin(t log s / 2)| ≤ |t| log s ≤ |t| (s - 1)`
  calc |(2 : ℝ) * Real.sin (Real.log s * t / 2)|
      ≤ |Real.log s * t| := abs_two_mul_sin_half_le _
    _ = |t| * Real.log s := by
        rw [abs_mul, abs_of_nonneg (Real.log_nonneg hs)]
        ring
    _ ≤ |t| * (s - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hs0) (abs_nonneg t)

end Work.BMF
