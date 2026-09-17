import Mathlib
import Submission.Commons.GeometryOfNumbers.Counting.card_int_points_ball_le_volume
import Submission.Commons.GeometryOfNumbers.Counting.lattice_log_sum_bound
import Submission.Commons.Analysis.SpecialFunctions.ExpLog.one_add_pow_le_exp

namespace Commons.GeometryOfNumbers.Counting

open MeasureTheory Metric

/-- For `1 ≤ d`, `1 ≤ R` and `(d : ℝ) ^ (3/2) ≤ R`, the slack `√d / 2` in the radius of the
counting ball can be absorbed at the cost of a factor `2`: `(R + √d / 2) ^ d ≤ 2 * R ^ d`. -/
theorem pow_add_sqrt_half_le_two_mul_pow {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 1 ≤ R)
    (hRbig : (d : ℝ) ^ (3 / 2 : ℝ) ≤ R) :
    (R + Real.sqrt d / 2) ^ d ≤ 2 * R ^ d := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  -- `(d : ℝ) ^ (3/2) = √d * d`
  have hrpow : (d : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt (d : ℝ) * (d : ℝ) := by
    have h1 : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
    rw [h1, Real.rpow_add_one (ne_of_gt hd0), ← Real.sqrt_eq_rpow]
  have hsd_le : Real.sqrt (d : ℝ) * (d : ℝ) ≤ R := by rw [← hrpow]; exact hRbig
  have hfactor : R + Real.sqrt (d : ℝ) / 2 = R * (1 + Real.sqrt (d : ℝ) / (2 * R)) := by
    field_simp
  have hpow : (R + Real.sqrt (d : ℝ) / 2) ^ d
      = R ^ d * (1 + Real.sqrt (d : ℝ) / (2 * R)) ^ d := by
    rw [hfactor, mul_pow]
  have hu_nonneg : 0 ≤ Real.sqrt (d : ℝ) / (2 * R) := by positivity
  have hbase : (1 + Real.sqrt (d : ℝ) / (2 * R)) ^ d ≤ 2 := by
    refine le_trans
      (Commons.Analysis.SpecialFunctions.ExpLog.one_add_pow_le_exp d _ hu_nonneg) ?_
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_half_le_two
    have hdd : (d : ℝ) * Real.sqrt (d : ℝ) ≤ R := by
      calc (d : ℝ) * Real.sqrt (d : ℝ) = Real.sqrt (d : ℝ) * (d : ℝ) := by ring
        _ ≤ R := hsd_le
    have h2R : (0 : ℝ) < 2 * R := by positivity
    calc (d : ℝ) * (Real.sqrt (d : ℝ) / (2 * R))
        = (d : ℝ) * Real.sqrt (d : ℝ) / (2 * R) := by ring
      _ ≤ R / (2 * R) := div_le_div_of_nonneg_right hdd h2R.le
      _ = 1 / 2 := by field_simp
  rw [hpow]
  calc R ^ d * (1 + Real.sqrt (d : ℝ) / (2 * R)) ^ d ≤ R ^ d * 2 :=
        mul_le_mul_of_nonneg_left hbase (pow_nonneg hRpos.le d)
    _ = 2 * R ^ d := by ring

theorem card_int_points_ball_le_two_omega {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 1 ≤ R)
    (hRbig : (d : ℝ) ^ (3 / 2 : ℝ) ≤ R) :
    (Nat.card {x : Fin d → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} : ℝ)
      ≤ 2 * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
          * R ^ d := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  set ω : ℝ := (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal with hω
  have hωnn : 0 ≤ ω := ENNReal.toReal_nonneg
  have h1 := card_int_points_le_volume d hd hRpos
  have hkey := pow_add_sqrt_half_le_two_mul_pow hd hR hRbig
  calc (Nat.card {x : Fin d → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} : ℝ)
      ≤ (R + Real.sqrt d / 2) ^ d * ω := h1
    _ ≤ (2 * R ^ d) * ω := mul_le_mul_of_nonneg_right hkey hωnn
    _ = 2 * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal * R ^ d := by
        rw [hω]; ring

end Commons.GeometryOfNumbers.Counting
