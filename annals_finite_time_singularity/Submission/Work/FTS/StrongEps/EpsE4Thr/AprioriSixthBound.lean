import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.AprioriSixth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-six loop**: for an honest `HQo α 6` profile, the squared `ℋ⁶`-norm is dominated by
the diagonal of the concrete pairing `IP6 1 … 1`.  This is `IP6_lo_coeffs` at `α₂ = 1`. -/
theorem HkSq_le_IP6 {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    Work.Spaces.HkSq α 6 f
      ≤ Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α f f :=
  Work.FTS.StrongPersist.IP6_lo_coeffs (α₂ := 1) one_pos
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl α hα f ⟨hsm, hmem⟩


end Work.FTS.StrongEps.EpsE4Thr
