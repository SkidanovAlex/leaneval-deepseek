import Mathlib
import Submission.Work.Thom.cupDeltaInfra
-- Re-pointed (Islands subproject, 2026): `Submission/Work/Thom/Relocate/PdSplitKc.lean` is a
-- verbatim copy of `Submission/Work/Cohomology/pd_split_kc.lean` with two imports re-routed.
-- The original chain has now itself been re-routed (`Crux/vk_transgression_cap_weak.lean`
-- imports `ovlRestrSurjCompat` instead of the duplicate `vkCruxCompat`), so the copy is no
-- longer needed: we import the original, which declares exactly the same names.
import Submission.Work.Cohomology.pd_split_kc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Work.Thom

/-- The underlying cochain of a restricted relative cochain is the pullback of the underlying
cochain along the inclusion. -/
theorem relRestrCochain_coe {X : TopCat} (A : Set X) (W : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n)) :
    (Work.Thom.relRestrCochain A W n t).1
      = t.1.comp ((Work.Cohomology.chainMap ℤ (TopCat.of ↥W) X
          (Work.Cohomology.subtypeIncl X W)).f n).hom := by
  rw [Work.Thom.relRestrCochain]
  rfl

/-- The coboundary of the restriction of a relative cocycle to a subspace vanishes; i.e. the
restriction of a relative cocycle is again a cocycle. -/
theorem relRestrCochain_dcocycle {X : TopCat} (A : Set X) (W : Set X) (n : ℕ)
    (t : ↥((Work.Cohomology.relComplex ℤ X A).X n))
    (ht : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t.1 = 0) :
    Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥W))
      (Work.Thom.relRestrCochain A W n t).1 = 0 := by
  rw [relRestrCochain_coe A W n t,
    Work.Cohomology.PDSplitKC.pd_kc_cochainDiff_pullback
      (Work.Cohomology.subtypeIncl X W) n t.1,
    ht, LinearMap.zero_comp]

end Work.Thom
