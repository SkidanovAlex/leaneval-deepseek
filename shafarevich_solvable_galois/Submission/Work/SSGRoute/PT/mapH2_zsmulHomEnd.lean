import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.SSGRoute.PT.AlphaTwoKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.SSGRoute.PT

/-- **`mapH2` of multiplication by an integer `k` is multiplication by `k` on `H²`.**

The coefficient endomorphism `zsmulHomEnd k C : C →+ C`, `c ↦ k • c`, is `G`-equivariant, and the
induced map `H²(G,C) → H²(G,C)` is just the scalar multiplication by `k` on the (additive group)
`H²(G,C)`.  This is the `ℤ`-scalar companion of `Work.SSGRoute.PT.mapH2_eq_nsmul`.

The proof reduces a class to a representative continuous `2`-cocycle `c` (`H2_induction_on`), where
`mapH2` acts by postcomposition with `c ↦ k • c` (`mapH2_H2π`, `mapZ2_apply`), and then uses that
`H2π` is additive, hence `ℤ`-linear (`map_zsmul`). -/
theorem mapH2_zsmulHomEnd {G : Type u} [TopologicalSpace G] [Group G] {C : Type v}
    [AddCommGroup C] [DistribMulAction G C] (k : ℤ)
    (h : Work.GroupCohomology.IsEquivariant G (Work.SSGRoute.PT.zsmulHomEnd k C))
    (y : Work.AbsoluteKummer.H2 G C) :
    Work.AbsoluteKummer.mapH2 (Work.SSGRoute.PT.zsmulHomEnd k C) h y = k • y := by
  refine Work.AbsoluteKummer.SES.H2_induction_on y
    (C := fun z => Work.AbsoluteKummer.mapH2 (Work.SSGRoute.PT.zsmulHomEnd k C) h z = k • z) ?_
  intro c
  rw [Work.AbsoluteKummer.mapH2_H2π]
  have hmap : Work.AbsoluteKummer.mapZ2 (Work.SSGRoute.PT.zsmulHomEnd k C) h c = k • c := by
    refine Subtype.ext (funext (fun q => ?_))
    simp [Work.AbsoluteKummer.mapZ2_apply, Work.SSGRoute.PT.zsmulHomEnd_apply]
  rw [hmap, map_zsmul]

end Work.SSGRoute.PT
