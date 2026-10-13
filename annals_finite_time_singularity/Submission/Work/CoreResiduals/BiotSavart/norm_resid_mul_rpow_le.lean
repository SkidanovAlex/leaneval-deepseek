import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- Weighted form of the crude residual bound `norm_resid_le_crude`: multiplying by the
homogeneous weight `‖y‖ ^ c` converts the two `‖y‖ ^ (-2)`, `‖y‖ ^ (-3)` factors into
`‖y‖ ^ (c - 2)`, `‖y‖ ^ (c - 3)` (the case `y = 0` being immediate). -/
theorem norm_resid_mul_rpow_le {c : ℝ} (hc : 0 < c) (h y : Work.LWP.R3) :
    ‖y‖ ^ c * ‖Work.CoreResiduals.BiotSavart.resid h y‖
      ≤ ‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ) + ‖y‖ ^ (c - 2) + 4 * ‖h‖ * ‖y‖ ^ (c - 3) := by
  by_cases hy : ‖y‖ = 0
  · rw [hy, Real.zero_rpow (ne_of_gt hc), zero_mul, zero_mul, zero_add]
    have h1 : 0 ≤ (0:ℝ) ^ (c - 2) := Real.rpow_nonneg le_rfl _
    have h2 : 0 ≤ 4 * ‖h‖ * (0:ℝ) ^ (c - 3) := by positivity
    linarith
  · have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
    have hcrude := norm_resid_le_crude h y
    have hmul := mul_le_mul_of_nonneg_left hcrude (Real.rpow_nonneg (norm_nonneg y) c)
    have h2 : ‖y‖ ^ c * ‖y‖ ^ (-2:ℝ) = ‖y‖ ^ (c - 2) := by
      rw [← Real.rpow_add hypos, show c + (-2:ℝ) = c - 2 by ring]
    have h3 : ‖y‖ ^ c * ‖y‖ ^ (-3:ℝ) = ‖y‖ ^ (c - 3) := by
      rw [← Real.rpow_add hypos, show c + (-3:ℝ) = c - 3 by ring]
    calc ‖y‖ ^ c * ‖resid h y‖
        ≤ ‖y‖ ^ c * (‖y + h‖ ^ (-2:ℝ) + ‖y‖ ^ (-2:ℝ) + 4 * ‖y‖ ^ (-3:ℝ) * ‖h‖) := hmul
      _ = ‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ) + ‖y‖ ^ (c - 2) + 4 * ‖h‖ * ‖y‖ ^ (c - 3) := by
          have h4 : ‖y‖ ^ c * (4 * ‖y‖ ^ (-3:ℝ) * ‖h‖) = 4 * ‖h‖ * ‖y‖ ^ (c - 3) := by
            rw [← h3]; ring
          rw [mul_add, mul_add, h2, h4]

end Work.CoreResiduals.BiotSavart
