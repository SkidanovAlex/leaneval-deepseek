import Mathlib
import Submission.Work.DISC.sections_disc
import Submission.Work.ANALYTIC.CechPt.exists_lcCurry
import Submission.Work.ATOM.ZS.Unred.LCZ

/-!
# Preliminaries for `sd ℤ[T] ≅ C(T,ℤ)_disc`

This module collects the small technical lemmas used by
`Submission/Work/ANALYTIC/CechPt/sd_zf_iso_Cdisc.lean` to identify the single dual
`ℤ[T] ⟹ 𝟙` of the free light condensed abelian group on a light profinite set `T` with the
discrete locally constant functions `Cdisc T = LC(-,ℤ)`.

Contents:

* `homFreeLinearEquiv` — the comparison `Hom(ℤ[S], A) ≅ A(S)` of the free–forgetful adjunction,
  upgraded from an `Equiv` to a `LinearEquiv` (i.e. `homFreeEquiv` is ℤ-linear);
* `prodMap` — the map `(s,t) ↦ (s, f t)` on the underlying spaces;
* `sdPhi_natural` — naturality in the light profinite set of the section identification
  `sdPhi : (ℤ[S] ⟹ ΔM)(T) ≅ C(S × T, M)`;
* `lcCurryEquiv_comap` — compatibility of the currying of locally constant functions with
  restriction maps;
* `lcDiscIntIso` — `lcDisc ℤ ≅ 𝟙`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite

noncomputable section

namespace Work.ANALYTIC.CechPt

/-! ## Linearity of the free–forgetful comparison -/

/-- **The comparison `Hom(ℤ[S], A) ≅ A(S)` is additive.**  This is `Work.DISC.homFreeEquiv`
(evaluation of a morphism at the canonical generator) together with the observation that
evaluation of the section map at a fixed element is additive. -/
noncomputable def homFreeAddEquiv (S : LightProfinite.{0}) (A : LightCondAb) :
    (Work.DISC.zfree S ⟶ A) ≃+ ↥(A.obj.obj (Opposite.op S)) where
  toFun := ⇑(Work.DISC.homFreeEquiv S A)
  invFun := ⇑(Work.DISC.homFreeEquiv S A).symm
  left_inv := fun g => (Work.DISC.homFreeEquiv S A).left_inv g
  right_inv := fun x => (Work.DISC.homFreeEquiv S A).right_inv x
  map_add' := by
    intro g g'
    simp only [Work.DISC.homFreeEquiv_eq_eval, CategoryTheory.Sheaf.Hom.add_app,
      ModuleCat.hom_add, LinearMap.add_apply]

/-- **The comparison `Hom(ℤ[S], A) ≅ A(S)` is ℤ-linear.**  This is `Work.DISC.homFreeEquiv`,
upgraded from a bijection to a `ℤ`-linear equivalence through the additivity above (an additive
map between abelian groups is `ℤ`-linear). -/
noncomputable def homFreeLinearEquiv (S : LightProfinite.{0}) (A : LightCondAb) :
    (Work.DISC.zfree S ⟶ A) ≃ₗ[ℤ] ↥(A.obj.obj (Opposite.op S)) :=
  @AddEquiv.toIntLinearEquiv (Work.DISC.zfree S ⟶ A) ↥(A.obj.obj (Opposite.op S)) _ _
    inferInstance inferInstance (homFreeAddEquiv S A)

/-- The linear comparison is the same function as `homFreeEquiv`. -/
theorem homFreeLinearEquiv_apply (S : LightProfinite.{0}) (A : LightCondAb)
    (g : Work.DISC.zfree S ⟶ A) :
    homFreeLinearEquiv S A g = Work.DISC.homFreeEquiv S A g := rfl

/-! ## The map `(s,t) ↦ (s, f t)` -/

/-- The map `(s,t) ↦ (s, f t)` on the underlying spaces of `S × T → S × T'`.  Its domain is
written as the product type so that `LocallyConstant.comap` applies without transparency
issues. -/
def prodMap (S : LightProfinite.{0}) {T T' : LightProfinite.{0}} (f : T ⟶ T') :
    C(↥S.toTop × ↥T.toTop, ↥S.toTop × ↥T'.toTop) :=
  ⟨fun p => (p.1, TopCat.Hom.hom f.hom p.2), by fun_prop⟩

theorem prodMap_apply (S : LightProfinite.{0}) {T T' : LightProfinite.{0}} (f : T ⟶ T')
    (p : ↥S.toTop × ↥T.toTop) :
    prodMap S f p = (p.1, TopCat.Hom.hom f.hom p.2) := rfl

/-! ## Naturality of `sdPhi` -/

section

set_option backward.isDefEq.respectTransparency false

/-- **Naturality of `sdPhi` in the light profinite set.**  Restricting a morphism
`ℤ[T'] ⟶ ℤ[S] ⟹ ΔM` along `zmap f` corresponds, under `sdPhi`, to restricting a locally constant
function on `S × T'` along `id × f`.

This is `Work.DISC.sdPhi_shift` with an arbitrary map of light profinite sets in place of the
shift of `ℕ∪{∞}`. -/
theorem sdPhi_natural (M : ModuleCat.{0} ℤ) (S T T' : LightProfinite.{0}) (f : T ⟶ T')
    (g : Work.DISC.zfree T' ⟶ (CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)) :
    Work.DISC.sdPhi M S T (Work.DISC.zfreeFunctor.map f ≫ g) =
      LocallyConstant.comap (prodMap S f) (Work.DISC.sdPhi M S T' g) := by
  rw [Work.DISC.sdPhi_apply, Work.DISC.sdPhi_apply, MonoidalClosed.uncurry_natural_left]
  have h1 : (Work.DISC.freeTensorIso S T).inv ≫
        (Work.DISC.zfree S ◁ Work.DISC.zfreeFunctor.map f) ≫ MonoidalClosed.uncurry g =
      Work.DISC.zfreeFunctor.map (S ◁ f) ≫
        ((Work.DISC.freeTensorIso S T').inv ≫ MonoidalClosed.uncurry g) := by
    rw [← Category.assoc, Work.DISC.freeTensorIso_inv_natural S f, Category.assoc]
  rw [h1, Work.DISC.homFreeEquiv_naturality, Work.DISC.lcDisc_map]
  congr 1

end

/-! ## Compatibility of currying with restriction -/

/-- The currying equivalence of `Submission.Work.ANALYTIC.CechPt.exists_lcCurry`, on elements. -/
theorem lcCurryEquiv_apply (S T : LightProfinite.{0}) (M : ModuleCat.{0} ℤ)
    (φ : LocallyConstant (↥S.toTop × ↥T.toTop) ↥M) (t : ↥T.toTop) (s : ↥S.toTop) :
    lcCurryEquiv S T M φ t s = φ (s, t) := rfl

/-- **Currying commutes with restriction.**  Currying a locally constant function and then
restricting in the outer variable is the same as restricting along `id × f` and then currying. -/
theorem lcCurryEquiv_comap (S : LightProfinite.{0}) (M : ModuleCat.{0} ℤ) {T T' : LightProfinite.{0}}
    (f : T ⟶ T') (φ : LocallyConstant (↥S.toTop × ↥T'.toTop) ↥M) :
    lcCurryEquiv S T M (LocallyConstant.comap (prodMap S f) φ) =
      LocallyConstant.comap (TopCat.Hom.hom f.hom) (lcCurryEquiv S T' M φ) := by
  ext t s
  rw [lcCurryEquiv_apply, LocallyConstant.coe_comap_apply, prodMap_apply]
  rw [LocallyConstant.coe_comap_apply, lcCurryEquiv_apply]

/-! ## The unit of `LightCondAb` -/

/-- `lcDisc ℤ ≅ 𝟙`: the locally constant ℤ-valued sheaf is the unit (equivalently, the constant
sheaf at `ℤ`). -/
noncomputable def lcDiscIntIso : Work.DISC.lcDisc (ModuleCat.of ℤ ℤ) ≅ (𝟙_ LightCondAb) :=
  (LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).app (ModuleCat.of ℤ ℤ)

end Work.ANALYTIC.CechPt
