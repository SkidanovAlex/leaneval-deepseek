import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.Sha2Lib.isLocTrivialLevel_inflH
import Submission.Work.SSGRoute.ext_corestriction

namespace Work.SSGRoute

open CategoryTheory CategoryTheory.Limits

/-- **Transitivity of the restriction of `Ext`-cohomology to subgroups.**  For `D ≤ E ≤ G`,
restricting a class `h ∈ Hⁿ(G, A)` to `D` is the same as first restricting it to `E` (which is the
`Ext`-class `extHRestrict E h` over the group `E`) and then further restricting along the inclusion
`D ↪ E`.

The content is the factorisation `Rep.resFunctor D.subtype = Rep.resFunctor E.subtype ⋙
Rep.resFunctor (Subgroup.inclusion hDE)` of restriction functors, which holds definitionally, and
the compatibility of `Ext.mapExactFunctor` with composition of exact functors
(`ext_mapExactFunctor_comp_functor_aux`). -/
theorem extHRestrict_eq_mapExactFunctor_inclusion {G : Type} [Group G] (D E : Subgroup G)
    (hDE : D ≤ E) {A : Rep SSGRoute.PTExt.Coeff G} {n : ℕ} (h : SSGRoute.PTExt.extH A n) :
    SSGRoute.PTExt.extHRestrict D h =
      (SSGRoute.PTExt.extHRestrict E h).mapExactFunctor
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (Subgroup.inclusion hDE : D →* E)) := by
  -- Replace both restrictions by the underlying `mapExactFunctor` of the restriction functor.
  have hD : SSGRoute.PTExt.extHRestrict D h =
      SSGRoute.PTExt.extRes (D.subtype : D →* G) h := by
    rw [SSGRoute.PTExt.extHRestrict, SSGRoute.PTExt.extHMap, Abelian.Ext.comp_mk₀_id]
    exact Abelian.Ext.mk₀_id_comp _
  have hE : SSGRoute.PTExt.extHRestrict E h =
      SSGRoute.PTExt.extRes (E.subtype : E →* G) h := by
    rw [SSGRoute.PTExt.extHRestrict, SSGRoute.PTExt.extHMap, Abelian.Ext.comp_mk₀_id]
    exact Abelian.Ext.mk₀_id_comp _
  rw [hD, hE, SSGRoute.PTExt.extRes, SSGRoute.PTExt.extRes]
  -- `Rep.resFunctor D.subtype` is definitionally `Rep.resFunctor E.subtype ⋙
  -- Rep.resFunctor (Subgroup.inclusion hDE)`, so the composed exact functor lemma applies.
  exact (ext_mapExactFunctor_comp_functor_aux
    (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (E.subtype : E →* G))
    (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (Subgroup.inclusion hDE : D →* E))
    n (SSGRoute.PTExt.unitRep G) A h).symm

theorem extHRestrict_eq_zero_of_le {G : Type} [Group G] (D E : Subgroup G) (hDE : D ≤ E)
    {A : Rep SSGRoute.PTExt.Coeff G} {n : ℕ} (h : SSGRoute.PTExt.extH A n)
    (h0 : SSGRoute.PTExt.extHRestrict E h = 0) : SSGRoute.PTExt.extHRestrict D h = 0 := by
  rw [extHRestrict_eq_mapExactFunctor_inclusion D E hDE h, h0,
    Abelian.Ext.mapExactFunctor_zero]
  rfl

end Work.SSGRoute
