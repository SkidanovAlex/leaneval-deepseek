import ChallengeDeps
import Submission.Basic
import Submission.Work.Distortion.one_le_distortion

/-!
# The small case of Pardon's bound

For `min p q ≤ 160` the target inequality `min p q / 160 ≤ distortion K` follows
from the universal lower bound `1 ≤ distortion K` for every knot, which is
`Work.Distortion.one_le_distortion`.  The mathematical content of the challenge is
therefore entirely in the case `min p q > 160`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Submission

/-- **The small case.**  If `min p q ≤ 160` then the target inequality holds for
every knot. -/
theorem target_of_small (p q : ℕ) (K : Knot) (hmin : Nat.min p q ≤ 160) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K := by
  have h : (Nat.min p q : ℝ≥0∞) ≤ 160 := by exact_mod_cast hmin
  have hle : (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ 1 := by
    have h' : (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ (1 / 160 : ℝ≥0∞) * 160 :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    rw [div_eq_mul_inv, one_mul, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)] at h'
    simpa [div_eq_mul_inv] using h'
  exact le_trans hle (Work.Distortion.one_le_distortion K)

end Submission
