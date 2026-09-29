import Mathlib
import Submission.Work.Fx.piDefs

namespace Work.Fx

/-- `2^(p+1) * √(2 - Aseq p)` is within `4^(-p)` of `π` (Mathlib's two-sided estimate for the
arctangent-free `sqrtTwoAddSeries` expansion of `π`), stated with the absolute value. -/
theorem pi_sqrtTwoAddSeries_abs (p : ℕ) :
    |(2 : ℝ) ^ (p + 1) * Real.sqrt (2 - Aseq p) - Real.pi| ≤ (1 / 4) ^ p := by
  have hlt : (2 : ℝ) ^ (p + 1) * Real.sqrt (2 - Aseq p) < Real.pi :=
    Real.pi_gt_sqrtTwoAddSeries p
  have hgt : Real.pi < (2 : ℝ) ^ (p + 1) * Real.sqrt (2 - Aseq p) + 1 / 4 ^ p :=
    Real.pi_lt_sqrtTwoAddSeries p
  have h44 : (1 : ℝ) / 4 ^ p = (1 / 4 : ℝ) ^ p := by rw [one_div, one_div, ← inv_pow]
  have h0 : 0 ≤ Real.pi - (2 : ℝ) ^ (p + 1) * Real.sqrt (2 - Aseq p) := by linarith
  rw [abs_sub_comm, abs_of_nonneg h0, ← h44]
  linarith

theorem piAseqSqrtBound (p : ℕ) :
    |(2 : ℝ) ^ (2 * p + 1) * Real.sqrt (2 - Aseq p) - (2 : ℝ) ^ p * Real.pi| ≤ (1 / 2) ^ p := by
  have habs := pi_sqrtTwoAddSeries_abs p
  have hpow : (2 : ℝ) ^ (2 * p + 1) = 2 ^ p * 2 ^ (p + 1) := by
    rw [← pow_add]; ring_nf
  rw [hpow]
  have hfac : 2 ^ p * 2 ^ (p + 1) * Real.sqrt (2 - Aseq p) - 2 ^ p * Real.pi
      = 2 ^ p * (2 ^ (p + 1) * Real.sqrt (2 - Aseq p) - Real.pi) := by ring
  rw [hfac]
  calc |2 ^ p * (2 ^ (p + 1) * Real.sqrt (2 - Aseq p) - Real.pi)|
      = 2 ^ p * |2 ^ (p + 1) * Real.sqrt (2 - Aseq p) - Real.pi| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ 2 ^ p * (1 / 4) ^ p := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = (1 / 2) ^ p := by rw [← mul_pow]; norm_num

end Work.Fx
