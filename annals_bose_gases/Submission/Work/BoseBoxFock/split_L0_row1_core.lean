import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.AntiNormal
import Submission.Work.BoseB4.DGamma_diag
import Submission.Work.BoseB4.DGamma_one
import Submission.Work.BoseB4.DGamma_quadform
import Submission.Work.BoseB4.Kafz_lower_bound_H2nd
import Submission.Work.BoseB4.Kafz_lower_bound_pointwise
import Submission.Work.BoseB4.TildeDataInst
import Submission.Work.BoseB4.a0_comp_a0d_sq
import Submission.Work.BoseB4.annC_creC_ccr
import Submission.Work.BoseB4.dGamma_diag_nonneg
import Submission.Work.BoseB4.monoOp_11_00_numOp
import Submission.Work.BoseB4.monoOp_lift_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem split_L0_row1_core {m : ℕ} [NeZero m]
    (B : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (y : ℕ →₀ Work.BoseB4.cfock (Work.BoseB4.Excited m)) :
    Work.BoseB4.a0d (Work.BoseB4.a0 (Work.BoseB4.lift B (Work.BoseB4.a0 y)))
      = (Work.BoseB4.monoOp 2 1 B - (2 : ℂ) • Work.BoseB4.monoOp 1 0 B) y := by
  -- Row 1 of `L0` (`L0 = ℓ⁻³Ŵ₁0 n₀ − μŴ₁0`): the operator `a₀† ∘ a₀ ∘ lift B ∘ a₀`
  -- is the anti-normal monomial combination `monoOp 2 1 B − 2 • monoOp 1 0 B`,
  -- i.e. `a₀†a₀a₀ = a₀²a₀† − 2a₀` (`Work.BoseB4.a0d_a0_a0_lift`) with the
  -- spectator `lift B` carried outside by commutation (`lift_a0`, `lift_a0d`).
  have h1 := LinearMap.congr_fun (Work.BoseB4.a0d_a0_a0_lift B) y
  simp only [LinearMap.comp_apply] at h1
  rw [Work.BoseB4.lift_a0d, Work.BoseB4.lift_a0] at h1
  exact h1

end Work.BoseBoxFock
