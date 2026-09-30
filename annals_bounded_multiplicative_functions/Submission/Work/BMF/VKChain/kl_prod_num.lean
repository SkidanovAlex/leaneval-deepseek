import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKChain

/-- Numeric bound: if `1000 ≤ log s` and `log s ≤ A/10^9` with `A > 0`, then
`(3 * log s / log 2 + 2) * (48 * π / A) ≤ 1`. -/
lemma kl_prod_num {s A : ℝ} (hApos : 0 < A) (hlog : Real.log s ≤ A / 10 ^ 9)
    (hlog1000 : 1000 ≤ Real.log s) :
    (3 * Real.log s / Real.log 2 + 2) * (48 * Real.pi / A) ≤ 1 := by
  have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have ht1000 : (1000:ℝ) ≤ Real.log s := hlog1000
  have htpos : 0 < Real.log s := by linarith
  have h9pos : (0:ℝ) < (10:ℝ)^9 := by norm_num
  have hDpos : 0 < (10:ℝ)^9 * Real.log s := mul_pos h9pos htpos
  -- `A ≥ 10^9 · log s`, from `log s ≤ A / 10^9`
  have hA_ge : (10:ℝ)^9 * Real.log s ≤ A := by
    have h := (le_div_iff₀ (show (0:ℝ) < 10^9 by norm_num)).mp hlog
    linarith
  -- first factor: `3 log s / log 2 + 2 ≤ 6 log s + 2`
  have hf1 : 3 * Real.log s / Real.log 2 + 2 ≤ 6 * Real.log s + 2 := by
    have h : 3 * Real.log s / Real.log 2 ≤ 3 * Real.log s / ((1:ℝ)/2) := by
      apply div_le_div_of_nonneg_left
      · show (0:ℝ) ≤ 3 * Real.log s; linarith [htpos]
      · norm_num
      · exact hlog2half
    have h2 : 3 * Real.log s / ((1:ℝ)/2) = 6 * Real.log s := by ring
    linarith [h, h2]
  -- second factor: `48 π / A ≤ 48 π / (10^9 · log s)`
  have hf2 : 48 * Real.pi / A ≤ 48 * Real.pi / ((10:ℝ)^9 * Real.log s) := by
    apply div_le_div_of_nonneg_left
    · positivity
    · exact hDpos
    · exact hA_ge
  have hprod : (3 * Real.log s / Real.log 2 + 2) * (48 * Real.pi / A) ≤
      (6 * Real.log s + 2) * (48 * Real.pi / ((10:ℝ)^9 * Real.log s)) := by
    apply mul_le_mul hf1 hf2
    · positivity
    · positivity
  -- final numeric estimate using `log s ≥ 1000` and `π ≤ 3.15`
  have hnum : (6 * Real.log s + 2) * (48 * Real.pi / ((10:ℝ)^9 * Real.log s)) ≤ 1 := by
    rw [mul_div_assoc']
    rw [div_le_one hDpos]
    nlinarith [Real.pi_lt_d2.le, ht1000]
  linarith [hprod, hnum]

end Work.BMF.VKChain
