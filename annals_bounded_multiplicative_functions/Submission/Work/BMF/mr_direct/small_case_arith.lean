import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- Arithmetic for the case `2 ≤ A ≤ 11 ≤ B` with constant `C1 ≥ 0`:
`3/2 + C1 * (log (B/11) / log 11 + 1 / log 11) ≤ (C1 + 20) * (log (B/A) / log A + 1 / log A)`.
Both bracket terms are nonnegative, and the second bracket dominates the first. -/
theorem small_case_arith (A B C1 : ℝ) (hA : 2 ≤ A) (hA11 : A ≤ 11) (hB : 11 ≤ B) (hC : 0 ≤ C1) :
    3 / 2 + C1 * (Real.log (B / 11) / Real.log 11 + 1 / Real.log 11)
      ≤ (C1 + 20) * (Real.log (B / A) / Real.log A + 1 / Real.log A) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  have hlog11 : 0 < Real.log 11 := Real.log_pos (by norm_num)
  have hlogA_le : Real.log A ≤ Real.log 11 := Real.log_le_log hA0 hA11
  have hlog11_le : Real.log 11 ≤ Real.log B := Real.log_le_log (by norm_num) hB
  -- Rewrite the two brackets in terms of `log B + 1`.
  have hb1 : Real.log (B / 11) / Real.log 11 + 1 / Real.log 11
      = (Real.log B + 1) / Real.log 11 - 1 := by
    rw [Real.log_div (ne_of_gt hB0) (by norm_num : (11 : ℝ) ≠ 0)]
    field_simp
    ring
  have hb2 : Real.log (B / A) / Real.log A + 1 / Real.log A
      = (Real.log B + 1) / Real.log A - 1 := by
    rw [Real.log_div (ne_of_gt hB0) (ne_of_gt hA0)]
    field_simp
    ring
  -- The second bracket dominates the first.
  have hb1_le_hb2 : (Real.log B + 1) / Real.log 11 - 1
      ≤ (Real.log B + 1) / Real.log A - 1 := by
    have h1 : 1 / Real.log 11 ≤ 1 / Real.log A := one_div_le_one_div_of_le hlogA hlogA_le
    have h2 : (Real.log B + 1) * (1 / Real.log 11) ≤ (Real.log B + 1) * (1 / Real.log A) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    rw [div_eq_mul_one_div (Real.log B + 1) (Real.log 11),
        div_eq_mul_one_div (Real.log B + 1) (Real.log A)]
    linarith
  have hA10 : Real.log A ≤ 10 := by
    have := Real.log_le_sub_one_of_pos hA0
    linarith
  -- `20 * bracket2 ≥ 43/2`, since `log A ≤ 10` and `log A ≤ log B`.
  have hkey : (43 / 2) * Real.log A ≤ 20 * (Real.log B + 1) := by
    have hBA : Real.log A ≤ Real.log B := le_trans hlogA_le hlog11_le
    nlinarith
  have hb2_ge : 3 / 2 ≤ 20 * ((Real.log B + 1) / Real.log A - 1) := by
    rw [show 20 * ((Real.log B + 1) / Real.log A - 1)
          = (20 * (Real.log B + 1)) / Real.log A - 20 by ring]
    rw [le_sub_iff_add_le, le_div_iff₀ hlogA]
    linarith
  rw [hb1, hb2]
  have hstep : C1 * ((Real.log B + 1) / Real.log 11 - 1)
      ≤ C1 * ((Real.log B + 1) / Real.log A - 1) :=
    mul_le_mul_of_nonneg_left hb1_le_hb2 hC
  nlinarith [hstep, hb2_ge]

end Work.BMF.mr_direct
