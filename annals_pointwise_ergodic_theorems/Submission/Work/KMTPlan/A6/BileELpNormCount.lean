import Mathlib
import Submission.Port.Aesm

namespace Work.KMTPlan.A6

open MeasureTheory ENNReal

/-- The `ℒ²`-seminorm (with respect to the counting measure on `ℤ`) of a complex sequence
whose squared absolute values are summable is the `ℓ²`-norm of the sequence, i.e. the square
root of the sum of the squares of the absolute values. -/
theorem BileELpNormCount (f : ℤ → ℂ) (hs : Summable fun n : ℤ => ‖f n‖ ^ 2) :
    MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
      = ENNReal.ofReal (Real.sqrt (∑' n : ℤ, ‖f n‖ ^ 2)) := by
  -- Unfold the `ℒ²` seminorm into the `ℝ≥0∞`-valued integral of `‖f n‖ ^ 2`.
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  -- The counting measure turns the integral into an `ℝ≥0∞`-valued series.
  rw [MeasureTheory.lintegral_count]
  -- Pass each term from `ℝ≥0∞` to `ℝ`.
  have hpt : ∀ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖f n‖ ^ 2) := by
    intro n
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num
  simp_rw [hpt]
  -- `ENNReal.ofReal` commutes with the (nonnegative, summable) series.
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs]
  -- The square root is the `1/2` power, and `ofReal` commutes with it.
  rw [ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg (fun n => by positivity)) (by norm_num : (0:ℝ) ≤ 1/2),
    Real.sqrt_eq_rpow]

end Work.KMTPlan.A6
