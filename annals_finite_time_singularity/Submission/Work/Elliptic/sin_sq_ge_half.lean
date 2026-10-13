import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.Elliptic

/-- On the interval `[π/4, π/2]` the square of `sin` is at least `1/2`.
Indeed `sin` is monotone on `[0, π/2]`, so `sin x ≥ sin (π/4) = √2/2 ≥ 0`, and
squaring preserves the inequality. -/
theorem sin_sq_ge_half {x : ℝ} (hx1 : π / 4 ≤ x) (hx2 : x ≤ π / 2) :
    (1 : ℝ) / 2 ≤ Real.sin x ^ 2 := by
  have hm : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin : Real.sin (π / 4) ≤ Real.sin x :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hx2 hx1
  have hsin' : √2 / 2 ≤ Real.sin x := by linarith [Real.sin_pi_div_four, hsin]
  have hprod : (√2 / 2) * (√2 / 2) ≤ Real.sin x * Real.sin x :=
    mul_le_mul hsin' hsin' (by positivity) hm
  have hprod' : (√2 / 2) ^ 2 ≤ Real.sin x ^ 2 := by simpa only [sq] using hprod
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

end Work.Elliptic
