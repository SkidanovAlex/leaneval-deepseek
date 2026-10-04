import Mathlib
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

lemma det_ne_zero_smul_add_one_of_nonneg_quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hA : ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (A.mulVec v)) :
    (t • A + (1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ)).det ≠ 0 := by
  -- the quadratic form of `t • A + (1 - t) • 1` dominates `(1 - t) * ‖v‖²`, and `1 - t > 0`
  have hlam : 0 < 1 - t := by linarith
  refine Work.Diff.STE.flat.det_ne_zero_of_quadForm_le _ hlam fun v => ?_
  rw [Work.Diff.STE.flat.sum_sum_mul_eq_dotProduct_quadForm]
  have hmul : (t • A + (1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec v
      = t • A.mulVec v + (1 - t) • v := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hmul, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hAq : 0 ≤ dotProduct v (A.mulVec v) := hA v
  have hvv : dotProduct v v = ∑ i, (v i) ^ 2 := by simp [dotProduct, pow_two]
  rw [hvv]
  nlinarith [mul_nonneg ht0 hAq]

end Work.Diff.STE.Lead
