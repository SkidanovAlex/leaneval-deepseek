import Mathlib
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_sq_eq_norm_ftLp

namespace Work.BourgainPlan.Maximal

/-- The `eLpNorm` of a square-summable sequence `h : ℤ → ℂ` with respect to the counting measure
equals the `ofReal` of the `L²(𝕋)`-norm of its Fourier transform `ftLp h hh`.

This is the counting-measure avatar of Parseval: by `eLpNorm_count_eq_tsum` the left-hand side is
`(∑' n, ofReal (‖h n‖ ^ 2)) ^ (1/2)`, the `tsum` of the `ofReal`s is the `ofReal` of the `ℓ²`-sum
(`ENNReal.ofReal_tsum_of_nonneg`), that sum is `‖ftLp h hh‖ ^ 2`
(`tsum_norm_sq_eq_norm_ftLp`), and `(x ^ 2) ^ (1/2) = x` for `x ≥ 0`. -/
theorem eLpNorm_count_ftLp {h : ℤ → ℂ} (hh : Memℓp h 2) :
    MeasureTheory.eLpNorm h (ENNReal.ofReal 2) MeasureTheory.Measure.count
      = ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.ftLp h hh‖ := by
  -- `Memℓp h 2` is exactly summability of `n ↦ ‖h n‖ ^ 2`.
  have hsumm : Summable (fun n : ℤ => ‖h n‖ ^ (2:ℝ)) := by
    simpa [Memℓp] using hh
  -- `ℓ²`-norm as a (possibly infinite) `eLpNorm` against the counting measure.
  rw [eLpNorm_count_eq_tsum h (by norm_num : (0:ℝ) < 2)]
  -- Push `ofReal` through the (summable) nonnegative `tsum`.
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm]
  -- Align the real exponent `(2 : ℝ)` with the natural power used by Parseval.
  have hpow : ∀ n : ℤ, ‖h n‖ ^ (2:ℝ) = ‖h n‖ ^ 2 := fun n => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [tsum_congr hpow]
  -- Parseval: the `ℓ²`-sum is the squared `L²(𝕋)`-norm of `ftLp h hh`.
  rw [Work.BourgainPlan.IonescuWainger.tsum_norm_sq_eq_norm_ftLp hh]
  -- `ofReal` of a nonnegative base commutes with `rpow`.
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
  congr 1
  -- `(x ^ 2) ^ (1/2) = x` for `x ≥ 0`.
  rw [← Real.rpow_natCast ‖Work.BourgainPlan.IonescuWainger.ftLp h hh‖ 2,
      ← Real.rpow_mul (norm_nonneg _) ((2:ℕ):ℝ) ((1:ℝ)/2)]
  norm_num

end Work.BourgainPlan.Maximal
