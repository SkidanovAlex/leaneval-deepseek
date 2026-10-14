import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.NNReal.Defs
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.exists_limG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)
open Work.FTS.Final
open Work.FTS.FinalClock
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG)

set_option autoImplicit false

/-- **The local duplicate is the frozen clause**: `LimApproxSE` (`LimApproxSE.lean`) and
`FinalV2.LimApprox` have the same body, so the two `Prop`s are equal (the `∀ T > 0` quantifier is
outermost in both; the inner form is `LimApproxOn`). -/
theorem limApproxSE_iff (α C₀ : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam) :
    LimApproxSE α C₀ Φs E g ↔ Work.FTS.FinalV2.LimApprox α C₀ Φs E g :=
  Iff.rfl

/-- The StrongEps copy `EllLimOK3` (`EpsLimitDefsG.lean`) IS the frozen FinalV2 clause. -/
theorem ellLimOK3_iff (α : ℝ) (E : Fn → Fn) :
    EllLimOK3 α E ↔ Work.FTS.FinalV2.EllLimOK3 α E := Iff.rfl


end Work.FTS.StrongEps
