import Mathlib
import Submission.Work.Resample.auRowDefs
import Submission.Work.ResMath.summable_exp_neg_affine_sq

/-!
# Summability of the Gaussian weight `auPsi`

`auPsi α s t k n = (1/(2α))·e^{−π(n − sk/t)²/α²}` is a Gaussian in the integer index `n`,
hence summable over `ℤ` as soon as `α ≠ 0`.  This is the summability input for the
row-sum identity `∑'_n auPsi α s t k n = ∑_j ‖(resA s t α) k j‖`.
-/

set_option autoImplicit false

namespace Work.Resample

/-- The Gaussian `n ↦ e^{−a(n−b)²}` is summable over `ℤ` for `a > 0`. -/
private theorem summable_exp_neg_sq_sub (a b : ℝ) (ha : 0 < a) :
    Summable fun n : ℤ => Real.exp (-a * ((n : ℝ) - b) ^ 2) := by
  have h := Work.ResMath.summable_exp_neg_affine_sq a (-b) ha (t := 1) (by norm_num)
  refine h.congr fun n => ?_
  congr 1
  push_cast
  ring

theorem auPsiSummable (α s t k : ℕ) (hα : 0 < α) : Summable (Work.Resample.auPsi α s t k) := by
  have ha : 0 < Real.pi / (α : ℝ) ^ 2 := by positivity
  have hbase : Summable
      (fun n : ℤ => Real.exp (-(Real.pi / (α : ℝ) ^ 2) *
        ((n : ℝ) - (s : ℝ) * (k : ℝ) / (t : ℝ)) ^ 2)) :=
    summable_exp_neg_sq_sub _ _ ha
  refine (hbase.mul_left (1 / (2 * (α : ℝ)))).congr fun n => ?_
  simp only [auPsi]

end Work.Resample
