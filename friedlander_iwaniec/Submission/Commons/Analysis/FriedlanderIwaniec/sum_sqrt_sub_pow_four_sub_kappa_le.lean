import Mathlib
import Submission.Commons.Analysis.FriedlanderIwaniec.sum_sqrt_sub_pow_four_sub_integral_le
import Submission.Commons.Analysis.FriedlanderIwaniec.intervalIntegral_sqrt_sub_pow_four_mul

namespace Commons.Analysis.FriedlanderIwaniec

lemma sum_sqrt_sub_pow_four_sub_kappa_le {y : ℝ} (hy : 1 ≤ y) :
    |(∑ c ∈ Finset.range (⌊y⌋₊ + 1), Real.sqrt (y ^ 4 - (c:ℝ) ^ 4)) -
      (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * y ^ 3| ≤ y ^ 2 := by
  have h1 := sum_sqrt_sub_pow_four_sub_integral_le (y := y) hy
  have h2 := intervalIntegral_sqrt_sub_pow_four_mul (y := y) (by linarith)
  rw [h2] at h1
  exact h1

end Commons.Analysis.FriedlanderIwaniec
