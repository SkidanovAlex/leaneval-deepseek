import Mathlib
import Submission.Work.SSGRoute.PT.ClassFormation
import Submission.Work.SSGRoute.ShapiroSetup
import Submission.Work.SSGRoute.PT.shapiro_defs
import Submission.Work.SSGRoute.PT.shapiro_H2_lift_defs
import Submission.Work.SSGRoute.PT.shapiroLift_mem_Z2
import Submission.Work.SSGRoute.PT.isLocallyConstant_shapiroLift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lifting a continuous `2`-cocycle on `U` to a continuous `2`-cocycle on `G`

The Shapiro ("induction of cocycles") step of the argument: for an *open* subgroup `U ≤ G` of
*finite* index and a continuous `2`-cocycle `a` on `U` with values in a discrete `U`-module `M`,
there is a continuous `2`-cocycle `c` on `G` with values in the coinduced module
`Coind_U^G M = {f : G → M // ∀ g u, f (g*u) = u⁻¹ • f g}` whose value at the pair `(u,v)`, evaluated
at the identity of `G`, returns `a (u,v)`.

The cocycle is the Shapiro lift `shapiroLift U a` of
`Submission/Work/SSGRoute/PT/shapiro_H2_lift_defs.lean`,
`(shapiroLift U a) (g,h) = (x ↦ coord x • a (A g (xU), A h (g⁻¹ • xU)))`; its cocycle condition is
`Work.SSGRoute.PT.shapiroLift_mem_Z2` and its local constancy (the only place the topological
hypotheses on `U` are used) is `Work.SSGRoute.PT.isLocallyConstant_shapiroLift`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.SSGRoute.PT

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

/-- **Evaluation of the Shapiro lift at `1` on the diagonal `U × U`**: the pair `(u,v)` evaluated at
the identity element of `G` returns `a (u,v)`. -/
theorem shapiroLift_apply_one (a : U × U → M) (u v : U) :
    (shapiroLift U a ((u : G), (v : G)) : G → M) 1 = a (u, v) := by
  have hfix : (u : G)⁻¹ • ((1 : G) : G ⧸ U) = ((1 : G) : G ⧸ U) := by
    change (u : G)⁻¹ • Shapiro.basePoint 0 G U = Shapiro.basePoint 0 G U
    exact Shapiro.basePoint_smul_eq 0 G U u⁻¹
  have h1 : Shapiro.A 0 G U (u : G) ((1 : G) : G ⧸ U) = u := by
    change Shapiro.A 0 G U (u : G) (Shapiro.basePoint 0 G U) = u
    exact A_basePoint U u
  have h2 : Shapiro.A 0 G U (v : G) ((u : G)⁻¹ • ((1 : G) : G ⧸ U)) = v := by
    rw [hfix]
    change Shapiro.A 0 G U (v : G) (Shapiro.basePoint 0 G U) = v
    exact A_basePoint U v
  rw [shapiroLift_apply, coord_one, h1, h2, one_smul]

end

theorem shapiro_H2_lift {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (a : U × U → M) (ha : a ∈ Work.AbsoluteKummer.Z2 U M) :
    ∃ c ∈ Work.AbsoluteKummer.Z2 G (Work.SSGRoute.PT.Coind G U M),
      ∀ u v : U, c ((u : G), (v : G)) 1 = a (u, v) := by
  have hloc : Work.AbsoluteKummer.IsLocallyConstant a :=
    ((Work.AbsoluteKummer.mem_Z2_iff a).mp ha).2
  refine ⟨shapiroLift U a, ?_, fun u v => shapiroLift_apply_one U a u v⟩
  exact AddSubgroup.mem_inf.mpr
    ⟨shapiroLift_mem_Z2 U a ha, isLocallyConstant_shapiroLift U hU a hloc⟩

end Work.SSGRoute.PT
