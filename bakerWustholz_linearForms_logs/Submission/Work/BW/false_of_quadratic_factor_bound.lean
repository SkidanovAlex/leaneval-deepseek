import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BW

/-- If `α * β = ±1` and the "height" `max 1 ‖α‖ * max 1 ‖β‖` is at most `1 + c` with
`c < 1/5`, then `‖α - β‖ ^ 2 < 5`.  Indeed, writing `A = max 1 ‖α‖`, `B = max 1 ‖β‖`,
we have `A, B ≥ 1`, whence `A + B ≤ A * B + 1 ≤ 2 + c` and `0 ≤ c`; thus
`‖α - β‖ ≤ ‖α‖ + ‖β‖ ≤ A + B ≤ 2 + c < 11/5`, giving `‖α - β‖ ^ 2 < 121/25 < 5`. -/
theorem normSq_sub_lt_five (α β : ℂ) (c : ℝ) (hc : c < 1 / 5)
    (hM : max 1 ‖α‖ * max 1 ‖β‖ ≤ 1 + c) : ‖α - β‖ ^ 2 < 5 := by
  have hx1 : (1 : ℝ) ≤ max 1 ‖α‖ := le_max_left _ _
  have hy1 : (1 : ℝ) ≤ max 1 ‖β‖ := le_max_left _ _
  have hxle : ‖α‖ ≤ max 1 ‖α‖ := le_max_right _ _
  have hyle : ‖β‖ ≤ max 1 ‖β‖ := le_max_right _ _
  have hAB1 : (1 : ℝ) ≤ max 1 ‖α‖ * max 1 ‖β‖ := by
    have := mul_le_mul hx1 hy1 (by norm_num) (by linarith)
    simpa using this
  have hc0 : 0 ≤ c := by linarith
  have hsum : max 1 ‖α‖ + max 1 ‖β‖ ≤ 2 + c := by
    have h : max 1 ‖α‖ + max 1 ‖β‖ ≤ max 1 ‖α‖ * max 1 ‖β‖ + 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)]
    linarith
  have hnorm : ‖α - β‖ ≤ 2 + c := by
    have h1 : ‖α - β‖ ≤ ‖α‖ + ‖β‖ := norm_sub_le α β
    linarith
  have h2 : (2 + c) ^ 2 < 5 := by nlinarith [hc, hc0]
  have h1 : ‖α - β‖ ^ 2 ≤ (2 + c) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  linarith

theorem false_of_quadratic_factor_bound (α β : ℂ) (c : ℝ) (hc : c < 1 / 5)
    (hprod : α * β = 1 ∨ α * β = -1)
    (hM : max 1 ‖α‖ * max 1 ‖β‖ ≤ 1 + c)
    (hd : 5 ≤ ‖α - β‖ ^ 2) : False :=
  absurd hd (not_le.mpr (normSq_sub_lt_five α β c hc hM))

end Work.BW
