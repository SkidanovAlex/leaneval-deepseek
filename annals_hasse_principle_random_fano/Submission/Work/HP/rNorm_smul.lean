import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP

theorem rNorm_smul {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    rNorm (c • v) = |c| * rNorm v := by
  have h2 : ∑ i, ((c • v) i) ^ 2 = c ^ 2 * ∑ i, (v i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [rNorm, rNorm, h2, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end Work.HP
