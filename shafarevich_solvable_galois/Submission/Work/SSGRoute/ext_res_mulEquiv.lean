import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open CategoryTheory

section ResEquivalence

variable {k : Type*} [CommRing k] {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')

/-- **Restriction of representations along a group isomorphism is an equivalence of categories.**
The quasi-inverse is restriction along the inverse isomorphism; the unit and counit are given by
the identity linear map, which is intertwining because `e.symm (e g) = g` and `e (e.symm g) = g`. -/
theorem resFunctor_isEquivalence :
    (Rep.resFunctor (k := k) e.symm.toMonoidHom).IsEquivalence := by
  refine Functor.IsEquivalence.mk' (Rep.resFunctor (k := k) e.toMonoidHom) ?_ ?_
  · -- unit: `𝟭 (Rep k G) ≅ res e.symm ⋙ res e`
    refine NatIso.ofComponents (fun X => Iso.mk
      (Rep.ofHom ⟨LinearMap.id, fun g => by
        ext x; simp [MulEquiv.symm_apply_apply]⟩)
      (Rep.ofHom ⟨LinearMap.id, fun g => by
        ext x; simp [MulEquiv.symm_apply_apply]⟩)
      (by ext x; simp) (by ext x; simp)) ?_
    intro X Y f
    ext x
    simp
  · -- counit: `res e ⋙ res e.symm ≅ 𝟭 (Rep k G')`
    refine NatIso.ofComponents (fun Y => Iso.mk
      (Rep.ofHom ⟨LinearMap.id, fun g => by
        ext x; simp [MulEquiv.apply_symm_apply]⟩)
      (Rep.ofHom ⟨LinearMap.id, fun g => by
        ext x; simp [MulEquiv.apply_symm_apply]⟩)
      (by ext x; simp) (by ext x; simp)) ?_
    intro X Y f
    ext x
    simp

end ResEquivalence

/-- **Group change along a group isomorphism on `Ext`.**  If `e : G ≃* G'` is an isomorphism of
groups and `X Y : Rep Coeff G`, then restricting both variables along `e.symm` (the functor
`CategoryTheory.Rep.res e.symm.toMonoidHom : Rep Coeff G ⥤ Rep Coeff G'`) does not change `Ext¹`:

  `Ext¹_{G'}(res X, res Y) ≅ Ext¹_G(X, Y)`.

Reason: `Rep.res` along a *group isomorphism* is an equivalence of categories (its quasi-inverse is
`Rep.res` along the inverse isomorphism), and equivalences preserve `Ext`.  This is the abstract
step that lets E7a move between the decomposition group `↥(decomp k A)` and the Galois group
`Gal(κ̄/κ)` of the local field via `NK.FrobeniusBridge.localGaloisEquiv`. -/
theorem ext_res_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Nonempty (CategoryTheory.Abelian.Ext
        (Rep.res e.symm.toMonoidHom X) (Rep.res e.symm.toMonoidHom Y) 1 ≃+
      CategoryTheory.Abelian.Ext X Y 1) := by
  haveI : (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).IsEquivalence :=
    resFunctor_isEquivalence e
  refine ⟨(AddEquiv.ofBijective
    ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom X Y 1) ?_).symm⟩
  exact Functor.mapExt_bijective_of_preservesProjectiveObjects
    (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom) X Y 1

end Work.SSGRoute
