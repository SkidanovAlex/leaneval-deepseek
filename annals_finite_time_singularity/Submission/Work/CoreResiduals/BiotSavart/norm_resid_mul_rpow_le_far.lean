/-
# `Work.CoreResiduals.BiotSavart.norm_resid_mul_rpow_le_far` — the *weighted* far-field bound

The far-field `C^{1,1}` step of the construction consumes the second-order Taylor residual
`resid h y = kf (y + h) - kf y - kDerivCLM y h` of the Newtonian kernel in *weighted* form: the
homogeneous weight `‖y‖ ^ c` (with an arbitrary real exponent `c`, no positivity assumed) is
attached to the residual in the far regime `2‖h‖ ≤ ‖y‖`.

This file records that the weighting is immediate from the unweighted far bound
`Work.CoreResiduals.BiotSavart.norm_resid_le_far`:

  `‖resid h y‖ ≤ 1024 ‖h‖² ‖y‖^{-4}`   ⟹
  `‖y‖ ^ c ‖resid h y‖ ≤ 1024 ‖h‖² ‖y‖ ^ (c - 4)`,

the two powers of `‖y‖` combining by `Real.rpow_add`.  The degenerate case `y = 0` is immediate:
`2‖h‖ ≤ 0` forces `h = 0` as well, and then both residuals and both sides vanish (the `0 ^ 0`
convention of `Real.rpow` being harmless because the factor `‖h‖² = 0` kills the right-hand side).
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.BiotSavart.TaylorDefs
import Submission.Work.CoreResiduals.BiotSavart.norm_resid_le_far
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **Weighted far-field residual bound.**  In the far regime `2‖h‖ ≤ ‖y‖` the second-order
Taylor residual of the Newtonian kernel satisfies

  `‖y‖ ^ c ‖resid h y‖ ≤ 1024 ‖h‖² ‖y‖ ^ (c - 4)`

for *every* real exponent `c` (no sign restriction: the case `‖y‖ = 0` is degenerate and both
sides vanish). -/
theorem norm_resid_mul_rpow_le_far {c : ℝ} (h y : Work.LWP.R3) (hy : 2 * ‖h‖ ≤ ‖y‖) :
    ‖y‖ ^ c * ‖Work.CoreResiduals.BiotSavart.resid h y‖
      ≤ 1024 * ‖h‖ ^ (2:ℕ) * ‖y‖ ^ (c - 4) := by
  rcases eq_or_lt_of_le (norm_nonneg y) with hy0 | hypos
  · -- `y = 0`: the hypothesis forces `h = 0` and both sides vanish
    have hh0 : h = 0 := by
      rw [← norm_eq_zero]
      have h2 : 2 * ‖h‖ ≤ 0 := by
        have h2' := hy
        rw [← hy0] at h2'
        exact h2'
      linarith [norm_nonneg h]
    have hy00 : y = 0 := norm_eq_zero.mp hy0.symm
    rw [hh0, hy00]
    simp [Work.CoreResiduals.BiotSavart.resid]
  · -- `y ≠ 0`: multiply the unweighted far bound by the nonnegative weight `‖y‖ ^ c`
    have hfar := norm_resid_le_far h y hy
    have h4 : ‖y‖ ^ c * ‖y‖ ^ (-4:ℝ) = ‖y‖ ^ (c - 4) := by
      rw [← Real.rpow_add hypos]
      ring_nf
    calc ‖y‖ ^ c * ‖Work.CoreResiduals.BiotSavart.resid h y‖
        ≤ ‖y‖ ^ c * (1024 * ‖h‖ ^ (2:ℕ) * ‖y‖ ^ (-4:ℝ)) :=
          mul_le_mul_of_nonneg_left hfar (Real.rpow_nonneg (norm_nonneg y) c)
      _ = 1024 * ‖h‖ ^ (2:ℕ) * (‖y‖ ^ c * ‖y‖ ^ (-4:ℝ)) := by ring
      _ = 1024 * ‖h‖ ^ (2:ℕ) * ‖y‖ ^ (c - 4) := by rw [h4]

end Work.CoreResiduals.BiotSavart
