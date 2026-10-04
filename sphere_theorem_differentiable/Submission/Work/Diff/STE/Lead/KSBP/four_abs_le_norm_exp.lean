import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `4 |t| ≤ ‖e^{2πit} - 1‖` on the fundamental domain `|t| ≤ 1/2`

The chord `‖e^{2πit} - 1‖` of the unit circle is `2 |sin (π t)|`
(`Complex.norm_exp_I_mul_ofReal_sub_one`), and Jordan's inequality in the form
`Real.mul_abs_le_abs_sin` (`2/π · |x| ≤ |sin x|` for `|x| ≤ π/2`) applied at `x = π t` gives
`2 |t| ≤ |sin (π t)|`.  Multiplying by `2` yields the claim.  The constant `4` is optimal:
at `t = 1/2` both sides equal `2`.
-/

namespace Work.Diff.STE.Lead.KSBP

/-- Jordan's inequality on the fundamental domain of the sine: `2 |t| ≤ |sin (π t)|` for
`|t| ≤ 1/2`. -/
private lemma two_mul_abs_le_abs_sin_pi (t : ℝ) (ht : |t| ≤ 1 / 2) :
    2 * |t| ≤ |Real.sin (Real.pi * t)| := by
  have hbound : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
    nlinarith [ht, Real.pi_pos]
  have h := Real.mul_abs_le_abs_sin (x := Real.pi * t) hbound
  rw [abs_mul, abs_of_nonneg Real.pi_pos.le] at h
  have h2 : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  rwa [h2] at h

theorem four_abs_le_norm_exp (t : ℝ) (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) - 1‖ := by
  have harg : 2 * Real.pi * Complex.I * (t : ℂ) = Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by
    push_cast; ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hdiv : (2 * Real.pi * t) / 2 = Real.pi * t := by ring
  rw [hdiv, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith [two_mul_abs_le_abs_sin_pi t ht]

end Work.Diff.STE.Lead.KSBP
