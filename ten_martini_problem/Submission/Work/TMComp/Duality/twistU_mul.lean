import Mathlib
import Submission.Work.TMComp.Duality.Defs

namespace Work.TMComp.Duality

/-- The phase character never vanishes. -/
theorem ph_ne_zero (α : ℝ) (k : ℤ) : ph α k ≠ 0 := by
  rw [← norm_pos_iff, ph_norm]
  norm_num

theorem twistU_mul (α : ℝ) : Work.TMComp.Duality.twistU α * Work.TMComp.Duality.twistUinv α = 1 ∧ Work.TMComp.Duality.twistUinv α * Work.TMComp.Duality.twistU α = 1 := by
  constructor
  · refine coord_ext fun f p => ?_
    obtain ⟨m, n⟩ := p
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, twistU_coord,
      twistUinv_coord, show n * -m = -(m * n) by ring, ph_neg, neg_neg, ← mul_assoc,
      mul_inv_cancel₀ (ph_ne_zero α (m * n)), one_mul]
  · refine coord_ext fun f p => ?_
    obtain ⟨m, n⟩ := p
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, twistUinv_coord,
      twistU_coord, show -n * m = -(m * n) by ring, ph_neg, neg_neg, ← mul_assoc,
      mul_inv_cancel₀ (ph_ne_zero α (m * n)), one_mul]

end Work.TMComp.Duality
