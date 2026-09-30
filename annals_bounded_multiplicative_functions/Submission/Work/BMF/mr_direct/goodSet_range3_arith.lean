import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

theorem goodSet_range3_arith (K L S qq pp C_W α : ℝ) (hK : 3 ≤ K) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hqq : 0 ≤ qq) (hpp : 0 ≤ pp) (hCW : 0 < C_W) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    K * L * (C_W * (K * L + 2) * (40 * (S * qq) + 54 * pp))
      ≤ 100 * (C_W + 1) * (1 + 1 / α) * (K + 1) ^ 3 * (L + 1) ^ 2 * (S * qq + pp) := by
  -- nonnegativity of the basic building blocks
  have hSqq : 0 ≤ S * qq := mul_nonneg hS hqq
  have hR : 0 ≤ S * qq + pp := by linarith
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hKL : (0 : ℝ) ≤ K * L := mul_nonneg hK0 hL
  have hP : 0 ≤ K * L * (K * L + 2) := mul_nonneg hKL (by linarith)
  have hQ : 0 ≤ (K + 1) ^ 2 * (L + 1) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hCW0 : (0 : ℝ) ≤ C_W := le_of_lt hCW
  -- from 0 < α ≤ 1/4 we get α⁻¹ ≥ 4, hence 1 + α⁻¹ ≥ 5
  have hinv : (4 : ℝ) ≤ α⁻¹ := by
    have h := one_div_le_one_div_of_le hα hα1
    norm_num at h
    exact h
  have hunit : (5 : ℝ) ≤ 1 + α⁻¹ := by linarith
  -- the three scalar inequalities
  have h1 : 40 * (S * qq) + 54 * pp ≤ 54 * (S * qq + pp) := by nlinarith [hSqq]
  have h2 : K * L * (K * L + 2) ≤ (K + 1) ^ 2 * (L + 1) ^ 2 := by
    have hKL1 : K * L + 1 ≤ (K + 1) * (L + 1) := by nlinarith [hK, hL]
    have h0 : 0 ≤ K * L + 1 := by nlinarith [hK, hL]
    have hmm := mul_self_le_mul_self h0 hKL1
    nlinarith [hmm]
  have h3 : 54 * C_W ≤ 500 * (C_W + 1) := by nlinarith [hCW]
  have h4 : (500 : ℝ) ≤ 100 * (1 + α⁻¹) * (K + 1) := by
    have hK1 : (4 : ℝ) ≤ K + 1 := by linarith
    nlinarith [hunit, hK1]
  -- multiply each scalar inequality by the appropriate nonnegative factor
  have hR54 : (0 : ℝ) ≤ 54 * (S * qq + pp) := by linarith
  have hQR : (0 : ℝ) ≤ ((K + 1) ^ 2 * (L + 1) ^ 2) * (S * qq + pp) := mul_nonneg hQ hR
  have hfac : (0 : ℝ) ≤ (C_W + 1) * ((K + 1) ^ 2 * (L + 1) ^ 2) * (S * qq + pp) :=
    mul_nonneg (mul_nonneg (by linarith) hQ) hR
  have p1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCW0 hP)
  have p2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCW0) hR54
  have p3 := mul_le_mul_of_nonneg_right h3 hQR
  have p4 := mul_le_mul_of_nonneg_right h4 hfac
  rw [one_div]
  nlinarith [p1, p2, p3, p4]

end Work.BMF.mr_direct
