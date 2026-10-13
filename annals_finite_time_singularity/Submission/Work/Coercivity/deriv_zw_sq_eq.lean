import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.HardyZ
import Submission.Work.Coercivity.pz_mul_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

/-- Product rule for `z ↦ z · (u z θ · w z)²` on the open half-line: the radial weight `w`
and every `θ`-slice of the smooth function `u` are differentiable at `z > 0`, so the
Leibniz rule applies and gives `(u w)² + z ∂_z (u w)²`. -/
theorem deriv_zw_sq_eq {u : ℝ → ℝ → ℝ} (hu : Work.Coercivity.IBP u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
      = (u z θ * Work.Spaces.w z) ^ 2 + z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z := by
  have hzmem : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hsl : DifferentiableAt ℝ (fun z' => u z' θ) z :=
    ((Work.Spaces.hardyZ_contDiffOn_slice u hu.smooth hθ).contDiffAt
      (isOpen_Ioi.mem_nhds hzmem)).differentiableAt (by norm_num)
  have hw : DifferentiableAt ℝ (Spaces.w) z := (hasDerivAt_w (ne_of_gt hz)).differentiableAt
  have hg : DifferentiableAt ℝ (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z :=
    (hsl.mul hw).pow 2
  have hmain : deriv (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z
      = 1 * (u z θ * Spaces.w z) ^ 2
        + z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z :=
    HasDerivAt.deriv ((hasDerivAt_id z).mul hg.hasDerivAt)
  rw [hmain]; ring

end Work.Coercivity
