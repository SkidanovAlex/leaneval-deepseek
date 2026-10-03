/-
# `FIArea2/R6/BFun29` — `bFun η ≥ 2²⁸` on `0 < η < 3/32`

The exponent cap of the §9 lacunarity input is not intrinsic.  `sec9log`
(`R6/sec9ErrSum6_arith`) needs only `1 + 2(8 + K + 4) ≤ bFun η`, and `bFun η` is explicit:

  `bFun η = 2^{η⁻¹log η⁻¹+4} + 2^{η⁻¹log η⁻¹+1} + 4 ≥ 2^{η⁻¹log η⁻¹+4}`.

For `η < 3/32` one has `η⁻¹ > 32/3`, and `log(32/3) > 2.36`, so

  `η⁻¹ log η⁻¹  ≥  (32/3)·log(32/3)  >  24`,

giving `bFun η > 2²⁸`.  Since `2(8 + K + 4) ≤ 2²⁷ + 424 < 2²⁸` for `K ≤ 2²⁶ + 200`, the
lacunarity cap may be raised to `2²⁷` (see `R6/LacPropK`), which is what removes the hard region
of the per-modulus primitive-pair count.

The numeric key is `log(32/3) > 2.36`, proved by splitting `32/3 = 32/3`:
`log 32 > 5·0.6931471803` (`Real.log_two_gt_d9`) and `log 3 = ½log 9 = ½(3log 2 + log(9/8))
≤ ½(3·0.6931471808 + 1/8) < 1.1023`.
-/
import Mathlib
import Submission.Work.FITop4.Defs4

namespace Work.FIArea2.R6

/-- `log(32/3) > 2.36`. -/
private lemma log_32_div_3_gt : (2.36 : ℝ) < Real.log (32 / 3) := by
  have h32 : (3.4657 : ℝ) < Real.log 32 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9
    push_cast
    linarith
  have h3 : Real.log 3 < (1.1023 : ℝ) := by
    have h98 : Real.log (9 / 8 : ℝ) ≤ (9 : ℝ) / 8 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h9 : Real.log 9 = 3 * Real.log 2 + Real.log (9 / 8 : ℝ) := by
      rw [show (9 : ℝ) = 2 ^ (3 : ℕ) * (9 / 8) by norm_num,
        Real.log_mul (by positivity) (by norm_num), Real.log_pow]
      push_cast
      ring_nf
    have h3' : Real.log 3 = Real.log 9 / 2 := by
      rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    have := Real.log_two_lt_d9
    rw [h3', h9]
    linarith
  have hlog : Real.log (32 / 3) = Real.log 32 - Real.log 3 :=
    Real.log_div (by norm_num : (32:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)
  rw [hlog]; linarith

/-- `24 ≤ η⁻¹ · log η⁻¹` for `0 < η < 3/32`. -/
lemma inv_mul_log_inv_ge (η : ℝ) (h0 : 0 < η) (h1 : η < 3 / 32) :
    (24 : ℝ) ≤ η⁻¹ * Real.log η⁻¹ := by
  have ht : (32 / 3 : ℝ) < η⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ h0, div_mul_eq_mul_div,
      div_lt_one (by norm_num : (0 : ℝ) < 3)]
    linarith
  have ht1 : (1 : ℝ) < η⁻¹ := lt_trans (by norm_num) ht
  have ht0 : (0 : ℝ) < η⁻¹ := lt_trans one_pos ht1
  have hlogt : Real.log (32 / 3) ≤ Real.log η⁻¹ := Real.log_le_log (by norm_num) ht.le
  have hprod : (32 / 3) * Real.log (32 / 3) ≤ η⁻¹ * Real.log η⁻¹ :=
    mul_le_mul ht.le hlogt (by linarith [log_32_div_3_gt]) ht0.le
  have hkey : (24 : ℝ) ≤ (32 / 3) * Real.log (32 / 3) := by
    have := log_32_div_3_gt
    nlinarith
  exact le_trans hkey hprod

/-- **`bFun η ≥ 2²⁸`** for `0 < η < 3/32`. -/
theorem bFun_ge_two_pow_28 (η : ℝ) (h0 : 0 < η) (h1 : η < 3 / 32) :
    (2 : ℝ) ^ (28 : ℕ) ≤ Work.FITop4.bFun η := by
  have hkey := inv_mul_log_inv_ge η h0 h1
  have hb : Work.FITop4.bFun η
      = (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) + (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 1) + 4 := rfl
  rw [hb]
  have hpow : (2 : ℝ) ^ (28 : ℕ) ≤ (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by push_cast; linarith)
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 1) := by positivity
  linarith

end Work.FIArea2.R6
