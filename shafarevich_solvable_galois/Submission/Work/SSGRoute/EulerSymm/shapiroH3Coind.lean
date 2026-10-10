import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.PT.shapiro_H3_coind
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro's lemma in degree `3`, for the coinduced module (Euler-symmetry route)

This file records, in the namespace `Work.SSGRoute.EulerSymm`, the degree-`3` Shapiro isomorphism

  `H³(G, Coind_U^G M) ≃+ H³(U, M)`

for an open subgroup `U ≤ G` of finite index and a discrete `U`-module `M`.

The substance (evaluation-at-the-identity cochain map `phiC3`, the Shapiro lift `shapiroLift3`,
the homotopy correction `s2c`, the primitive `h3Primitive`, and the surjectivity/kernel halves
`shapiro_H3_lift`/`shapiro_H3_inj`) is developed in the modules of
`Submission/Work/SSGRoute/PT/shapiro_H3_*`; the theorem below is the packaged form required by the
Euler-symmetry route of the Shafarevich theorem.
-/

namespace Work.SSGRoute.EulerSymm

theorem shapiroH3Coind {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (hM : Work.AbsoluteKummer.IsDiscreteModule U M) :
    Nonempty (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.Coind G U M) G ≃+
      Work.SSGRoute.H3 (M := M) U) :=
  Work.SSGRoute.PT.shapiro_H3_coind U hU hM

end Work.SSGRoute.EulerSymm
