import Mathlib
import Submission.Work.CNum.Basic

/-!
# A quantitative lower bound for `sin t - sin s` on `[0, π/4]`

For `0 ≤ s ≤ t ≤ π/4` we have `(t - s) / 4 ≤ sin t - sin s`.

The proof uses the product formula `sin t - sin s = 2 sin((t-s)/2) cos((t+s)/2)`
(`Real.sin_sub_sin`), Jordan's inequality `2/π * x ≤ sin x` on `[0, π/2]`
(`Real.mul_le_sin`) and the lower bound `1/2 ≤ cos((t+s)/2)` coming from
`cos(π/4) = √2/2 ≥ 1/2` and the antitonicity of `cos` on `[0, π]`.
-/

namespace Work.CNum

theorem sin_sub_sin_ge {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (h1 : t ≤ Real.pi / 4) :
    (t - s) / 4 ≤ Real.sin t - Real.sin s := by
  rw [Real.sin_sub_sin]
  have hd : 0 ≤ t - s := by linarith
  have hd2 : 0 ≤ (t - s) / 2 := by linarith
  have hd2π : (t - s) / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hsin : 2 / Real.pi * ((t - s) / 2) ≤ Real.sin ((t - s) / 2) :=
    Real.mul_le_sin hd2 hd2π
  have hsin_nn : 0 ≤ Real.sin ((t - s) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hd2 (by linarith [Real.pi_pos])
  have hm0 : 0 ≤ (t + s) / 2 := by linarith
  have hm1 : (t + s) / 2 ≤ Real.pi / 4 := by linarith
  have hmπ : (t + s) / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hcos : (1 / 2 : ℝ) ≤ Real.cos ((t + s) / 2) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := (t + s) / 2) (y := Real.pi / 4) hm0
      (by linarith [Real.pi_pos]) hm1
    rw [Real.cos_pi_div_four] at h
    have h2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
    linarith
  have hstep : 2 * (2 / Real.pi * ((t - s) / 2)) * (1 / 2) ≤
      2 * Real.sin ((t - s) / 2) * Real.cos ((t + s) / 2) := by
    have h1' : (2 / Real.pi * ((t - s) / 2)) * (1 / 2) ≤
        Real.sin ((t - s) / 2) * Real.cos ((t + s) / 2) :=
      mul_le_mul hsin hcos (by norm_num) hsin_nn
    nlinarith [h1']
  have heq : 2 * (2 / Real.pi * ((t - s) / 2)) * (1 / 2) = (t - s) / Real.pi := by
    field_simp
  rw [heq] at hstep
  have hfin : (t - s) / 4 ≤ (t - s) / Real.pi :=
    div_le_div_of_nonneg_left hd Real.pi_pos (by linarith [Real.pi_lt_four])
  linarith [hfin, hstep]

end Work.CNum
