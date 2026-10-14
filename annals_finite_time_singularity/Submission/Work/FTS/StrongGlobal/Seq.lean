import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongGlobal.contDiffOn_concat_1
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongGlobal

open Work.FTS.Nonlin
open Work.FTS.Apriori
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn}

/-! ## Auxiliary facts -/




/-! ## The time steps -/

/-- The end of the `n`-th time step, `(n+1)δ`. -/
def stepEnd (δ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) * δ







/-! ## The accumulated pieces -/

/-- **The data carried by the `n`-th accumulated piece** of the continuation: it solves the dynamic
modulated problem on `[0, (n+1)δ]`, starts at `g₀`, and obeys the a-priori `ℋ⁴`-bound and the
persisted `ℋ⁶`-bound there. -/
structure PieceData (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g₀ : Fn) (δ C₀ K : ℝ) (n : ℕ)
    (g : Fam) : Prop where
  data : ∀ z θ, g z θ 0 = g₀ z θ
  sol : StrongSolOn α Φs EllSol 0 (stepEnd δ n) g
  bnd4 : ∀ τ ∈ Set.Icc 0 (stepEnd δ n), Xn α (slice g τ) ≤ C₀ * α ^ 2
  bnd6 : ∀ τ ∈ Set.Icc 0 (stepEnd δ n), Xn6 α (slice g τ) ≤ K * α ^ 2



end Work.FTS.StrongGlobal
