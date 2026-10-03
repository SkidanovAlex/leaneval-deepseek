import Mathlib

namespace Work.FIArea7.P231

/-- Auxiliary inequality used in the Friedlander–Iwaniec argument: for `M, N ≥ 1`,
`M √N + √(MN) ≤ 3 (M+N)^{1/12} (MN)^{11/12}`.
Both summands are dominated by `(M+N)^{1/12} (MN)^{11/12}`. -/
lemma sqrt_error_le {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    M * Real.sqrt N + Real.sqrt (M * N)
      ≤ 3 * ((M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12)) := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hM0' : (0:ℝ) ≤ M := le_of_lt hM0
  have hN0' : (0:ℝ) ≤ N := le_of_lt hN0
  have hMN0 : (0:ℝ) ≤ M * N := mul_nonneg hM0' hN0'
  have hP1 : (1:ℝ) ≤ (M + N) ^ ((1 : ℝ) / 12) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hQnn : (0:ℝ) ≤ (M * N) ^ ((11 : ℝ) / 12) := Real.rpow_nonneg hMN0 _
  -- First summand: `M √N ≤ (M+N)^{1/12} (MN)^{11/12}`.
  have h1 : M * Real.sqrt N ≤ (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) := by
    rw [Real.sqrt_eq_rpow]
    have hMle : M ≤ M ^ ((11:ℝ)/12) * (M + N) ^ ((1:ℝ)/12) := by
      have hsplit : M = M ^ ((11:ℝ)/12) * M ^ ((1:ℝ)/12) := by
        have h := Real.rpow_add hM0 ((11:ℝ)/12) ((1:ℝ)/12)
        rw [show (11:ℝ)/12 + (1:ℝ)/12 = (1:ℝ) by norm_num, Real.rpow_one] at h
        exact h
      conv_lhs => rw [hsplit]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hM0' (by linarith) (by norm_num)) (Real.rpow_nonneg hM0' _)
    calc M * N ^ ((1:ℝ)/2)
        ≤ M * N ^ ((11:ℝ)/12) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) hM0'
      _ ≤ M ^ ((11:ℝ)/12) * (M + N) ^ ((1:ℝ)/12) * N ^ ((11:ℝ)/12) :=
          mul_le_mul_of_nonneg_right hMle (Real.rpow_nonneg hN0' _)
      _ = (M + N) ^ ((1:ℝ)/12) * (M * N) ^ ((11:ℝ)/12) := by
          rw [Real.mul_rpow hM0' hN0']
          ring
  -- Second summand: `√(MN) ≤ (M+N)^{1/12} (MN)^{11/12}`.
  have h2 : Real.sqrt (M * N) ≤ (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) := by
    rw [Real.sqrt_eq_rpow]
    have hstep1 : (M * N) ^ ((1:ℝ)/2) ≤ (M * N) ^ ((11:ℝ)/12) :=
      Real.rpow_le_rpow_of_exponent_le (by nlinarith [hM, hN]) (by norm_num)
    have hstep2 : (M * N) ^ ((11:ℝ)/12)
        ≤ (M + N) ^ ((1:ℝ)/12) * (M * N) ^ ((11:ℝ)/12) := by
      have h := mul_le_mul_of_nonneg_right hP1 hQnn
      simpa using h
    linarith
  have hAB : (0:ℝ) ≤ (M + N) ^ ((1 : ℝ) / 12) * (M * N) ^ ((11 : ℝ) / 12) :=
    mul_nonneg (le_trans zero_le_one hP1) hQnn
  linarith [h1, h2, hAB]

end Work.FIArea7.P231
