import Mathlib
import Submission.Work.StemsB.WangE4
import Submission.Work.Pi6.EFACTS.Z.WangThetaLow
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The low-degree Wang transgression

`wangThetaLow b hb E p hp hT_O d_G hT_G : H^{b-1}(F) →ₗ[ℤ] H^0(F)` is the Wang transgression in the
lowest degree in which it is defined (the degree of the fundamental class of the fibre).  It is the
**geometric** transgression `ρ ∘ Σ_low ∘ λ_G^*` of the integral port
`Work.StemsB.wangThetaLow` (file `Submission/Work/Pi6/EFACTS/Z/WangThetaLow.lean`, a port of the
rational `Work.StemsB.Rat.wangThetaLow`), for which the multiplicativity
(`Work.Pi6.EFACTS.CollarZ.wangTheta_cup_mixed`, `…/wangTheta_cup_three`) and the exactness
(`Work.Pi6.EFACTS.wangExactLow`) are available.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Pi6.EFACTS

noncomputable section

/-- **The low transgression** `H^{b-1}(F) → H^0(F)` of the sphere fibration, i.e. the geometric
transgression `ρ ∘ Σ_low ∘ λ_G^*` of the integral port. -/
noncomputable def wangThetaLow (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) :
    Work.Cohomology.singularCohomology ℤ (b - 1) (Work.StemsB.wangCohFsp b p) →ₗ[ℤ]
      Work.Cohomology.singularCohomology ℤ 0 (Work.StemsB.wangCohFsp b p) :=
  Work.StemsB.wangThetaLow b hb E p d_G hT_G hT_O

end

end Work.Pi6.EFACTS
