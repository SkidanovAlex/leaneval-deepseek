import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- Arithmetic for the case `2 ≤ A ≤ B ≤ 11` with constant `K ≥ 0`:
`3/2 ≤ (K + 20) * (log (B/A) / log A + 1 / log A)`. -/
theorem small_case_arith_le_eleven (A B K : ℝ) (hA : 2 ≤ A) (hAB : A ≤ B) (hA11 : A ≤ 11)
    (hK : 0 ≤ K) :
    3 / 2 ≤ (K + 20) * (Real.log (B / A) / Real.log A + 1 / Real.log A) := by
  have hApos : 0 < A := by linarith
  have h1A : 1 < A := by linarith
  have hlogA_pos : 0 < Real.log A := Real.log_pos h1A
  have hBA1 : 1 ≤ B / A := by rw [one_le_div hApos]; exact hAB
  have hlogBA : 0 ≤ Real.log (B / A) := Real.log_nonneg hBA1
  have hlogA_le : Real.log A ≤ 40 / 3 := by
    have h1 : Real.log A ≤ Real.log 11 := Real.log_le_log (by linarith) hA11
    have h2 : Real.log 11 ≤ 10 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11)
      linarith
    linarith
  have hterm : 3 / 40 ≤ 1 / Real.log A := by
    rw [le_div_iff₀ hlogA_pos]
    nlinarith [hlogA_le]
  have hd1 : 0 ≤ Real.log (B / A) / Real.log A := div_nonneg hlogBA (le_of_lt hlogA_pos)
  have ht : 3 / 40 ≤ Real.log (B / A) / Real.log A + 1 / Real.log A := by linarith
  have h20 : (20 : ℝ) ≤ K + 20 := by linarith
  have := mul_le_mul h20 ht (by norm_num : (0 : ℝ) ≤ 3 / 40) (by linarith : (0 : ℝ) ≤ K + 20)
  have : (20 : ℝ) * (3 / 40) = 3 / 2 := by norm_num
  linarith

end Work.BMF.mr_direct
