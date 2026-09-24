import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

/-- The factor `T^η` with `T = M N = N^{6/5}` and `η = ε/2` is absorbed by `N^ε`. -/
theorem l4_rpow_absorb {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N) :
    (Submission.LargeValues.M N) ^ (ε / 2) ≤ (N : ℝ) ^ ε := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [Submission.LargeValues.M, ← Real.rpow_mul hN0]
  apply Real.rpow_le_rpow_of_exponent_le hN1
  linarith

end Work.GM.S3
