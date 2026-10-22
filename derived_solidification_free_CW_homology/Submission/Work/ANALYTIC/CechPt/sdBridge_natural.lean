import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualCechBridge

/-!
# Naturality of the bridge `sd ℤ[T] ≅ C(T,ℤ)_disc` in the light profinite set

The bridge `sdBridge T : sd (ℤ[T]) ≅ Cdisc T` of `DualCechBridge.lean` is the composite

`(ℤ[T] ⟹ 𝟙) ≅ (ℤ[T] ⟹ lcDisc ℤ) ≅ lcDisc (LC(T,ℤ))`

of the transport `lcDiscIntIso` (in the target) and the sectionwise comparison `sdIsoHom`.

This module proves `sdBridge_natural`: `sdBridge` is natural in `T`, i.e. for every map
`f : S ⟶ T` of light profinite sets the square

```
sd (ℤ[T]) --sdBridge T--> Cdisc T
   |                          |
 pre (zmap f)                 | LocallyConstant.comap f
   v                          v
sd (ℤ[S]) --sdBridge S--> Cdisc S
```

commutes.

## Route

Everything is computed on sections.  For a light profinite set `U`, a morphism
`a : ℤ[U] ⟶ A` has `homFreeEquiv U A a ∈ A(U)`, and

* `homFreeEquiv_comp` computes the sections of a composite: `a ≫ h ↦ h(U)(a)`;
* `sdIsoHom_app` identifies the `U`-component of `sdIsoHom S M` with `sdComp S M U`, which is
  the sectionwise map `lcCurryEquiv S U M ∘ sdPhi M S U` (`sdComp_homFreeEquiv`);
* `sdComp_pre` (the mathematical content) is the naturality of `sdComp` in the *free* variable:
  it follows from `uncurry_pre_app`, naturality of `freeTensorIso` in its first slot
  (`freeTensorIso_inv_natural_fst`), naturality of `homFreeEquiv` in the light profinite set, and
  the compatibility of `lcCurryEquiv` with restriction in the free variable
  (`lcCurryEquiv_comap_fst`);
* `ext_of_homFreeEquiv` reduces the equality of two morphisms of light condensed abelian groups
  to the equality of their `homFreeEquiv`-values on `a : ℤ[U] ⟶ _` for all `U`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite

noncomputable section

namespace Work.ANALYTIC.CechPt

/-! ## Auxiliary maps and section lemmas -/

/-- The map `(s,u) ↦ (f s, u)` on the underlying spaces: the free-variable analogue of
`prodMap`. -/
def prodMapFst {S T : LightProfinite.{0}} (f : S ⟶ T) (U : LightProfinite.{0}) :
    C(↥S.toTop × ↥U.toTop, ↥T.toTop × ↥U.toTop) :=
  ⟨fun p => (f.hom.hom p.1, p.2), by fun_prop⟩

theorem prodMapFst_apply {S T : LightProfinite.{0}} (f : S ⟶ T) (U : LightProfinite.{0})
    (p : ↥S.toTop × ↥U.toTop) : prodMapFst f U p = (f.hom.hom p.1, p.2) := rfl

/-- **Sections of a composite**: applying the section map of `h : A ⟶ B` at `U` to the section of
`A` corresponding to `a : ℤ[U] ⟶ A` is the same as evaluating `homFreeEquiv` on `a ≫ h`. -/
theorem homFreeEquiv_comp (U : LightProfinite.{0}) {A B : LightCondAb}
    (a : Work.DISC.zfree U ⟶ A) (h : A ⟶ B) :
    Work.DISC.homFreeEquiv U B (a ≫ h) =
      (ModuleCat.Hom.hom (h.hom.app (op U))) (Work.DISC.homFreeEquiv U A a) := rfl

/-- The `U`-component of `(LocallyConstant.functor ℤ).map φ` is postcomposition with `φ`. -/
theorem lcFunctor_map_app (M N : ModuleCat ℤ) (φ : M ⟶ N) (U : LightProfinite.{0})
    (v : LocallyConstant ↥U.toTop ↥M) :
    (ModuleCat.Hom.hom (((LightCondMod.LocallyConstant.functor ℤ).map φ).hom.app (op U))) v
      = LocallyConstant.map φ v := rfl

/-- The morphism underlying `sdBridge`. -/
theorem sdBridge_hom (T : LightProfinite.{0}) :
    (sdBridge T).hom =
      (CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv ≫
        sdIsoHom T (ModuleCat.of ℤ ℤ) := rfl

/-- `sdComp` evaluated on a morphism out of `ℤ[U]` is `lcCurryEquiv ∘ sdPhi`. -/
theorem sdComp_homFreeEquiv (S : LightProfinite.{0}) (M : ModuleCat ℤ) (U : LightProfinite.{0})
    (g : Work.DISC.zfree U ⟶ (CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)) :
    sdComp S M U (Work.DISC.homFreeEquiv U _ g) = lcCurryEquiv S U M (Work.DISC.sdPhi M S U g) := by
  rw [sdComp_apply, ← homFreeLinearEquiv_apply, LinearEquiv.symm_apply_apply, sdPhiLin_apply]

/-- `sdIsoHom` is the sectionwise comparison `sdComp`: this is the definition of `sdIsoHom` as the
preimage of `sdNatTrans`, whose components are `sdComp`. -/
theorem sdIsoHom_hom (S : LightProfinite.{0}) (M : ModuleCat ℤ) :
    (sdIsoHom S M).hom = sdNatTrans S M := by
  have hF : (sheafToPresheaf cechTop (ModuleCat ℤ)).map (sdIsoHom S M) =
      (sdIsoHom S M).hom := rfl
  rw [← hF]
  exact Functor.map_preimage _ _

theorem sdIsoHom_app (S : LightProfinite.{0}) (M : ModuleCat ℤ) (U : LightProfinite.{0})
    (y : ↥(((CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)).obj.obj
      (op U))) :
    (ModuleCat.Hom.hom ((sdIsoHom S M).hom.app (op U))) y = sdComp S M U y := by
  rw [sdIsoHom_hom]
  rfl

/-- `sdIsoHom` on a morphism out of `ℤ[U]`. -/
theorem sdIsoHom_homFreeEquiv (S : LightProfinite.{0}) (M : ModuleCat ℤ) (U : LightProfinite.{0})
    (g : Work.DISC.zfree U ⟶ (CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)) :
    Work.DISC.homFreeEquiv U (Work.DISC.lcDisc (ModuleCat.of ℤ (LocallyConstant ↥S.toTop ↥M)))
        (g ≫ sdIsoHom S M) = sdComp S M U (Work.DISC.homFreeEquiv U _ g) := by
  rw [homFreeEquiv_comp, sdIsoHom_app]

/-- The functor map `Cdisc T ⟶ Cdisc S` induced by `comapₗ` acts on sections by postcomposition. -/
theorem lcMap_homFreeEquiv {S T : LightProfinite.{0}} (f : S ⟶ T) (U : LightProfinite.{0})
    (w : Work.DISC.zfree U ⟶ (LightCondMod.LocallyConstant.functor ℤ).obj
      (ModuleCat.of ℤ (LocallyConstant ↥T.toTop ℤ))) :
    Work.DISC.homFreeEquiv U ((LightCondMod.LocallyConstant.functor ℤ).obj
        (ModuleCat.of ℤ (LocallyConstant ↥S.toTop ℤ)))
        (w ≫ (LightCondMod.LocallyConstant.functor ℤ).map
          (ModuleCat.ofHom (LocallyConstant.comapₗ ℤ f.hom.hom)))
      = LocallyConstant.map (LocallyConstant.comapₗ ℤ f.hom.hom)
          (Work.DISC.homFreeEquiv U ((LightCondMod.LocallyConstant.functor ℤ).obj
            (ModuleCat.of ℤ (LocallyConstant ↥T.toTop ℤ))) w) := by
  rw [homFreeEquiv_comp]
  exact lcFunctor_map_app (ModuleCat.of ℤ (LocallyConstant ↥T.toTop ℤ))
    (ModuleCat.of ℤ (LocallyConstant ↥S.toTop ℤ))
    (ModuleCat.ofHom (LocallyConstant.comapₗ ℤ f.hom.hom)) U _

/-! ## Naturality of `freeTensorIso` in the first variable -/

/-- `freeTensorIso` is natural in the first variable: this is `μ_natural_left` for the two
monoidal functors whose composite is `zfree`. -/
theorem freeTensorIso_natural_fst {S T : LightProfinite.{0}} (f : S ⟶ T)
    (U : LightProfinite.{0}) :
    (Work.DISC.freeTensorIso S U).hom ≫ Work.DISC.zfreeFunctor.map (f ▷ U) =
      (Work.ATOM.zmap f ▷ Work.DISC.zfree U) ≫ (Work.DISC.freeTensorIso T U).hom := by
  have hG := Functor.LaxMonoidal.μ_natural_left lightProfiniteToLightCondSet f U
  have hF := Functor.LaxMonoidal.μ_natural_left (LightCondensed.free (R := ℤ))
      (lightProfiniteToLightCondSet.map f) (lightProfiniteToLightCondSet.obj U)
  simp only [Work.DISC.freeTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.Monoidal.μIso_hom, Work.DISC.zfreeFunctor, Work.ATOM.zmap, Functor.comp_obj,
    Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp, ← hG, Functor.map_comp, ← Category.assoc, ← hF, Category.assoc]

theorem freeTensorIso_inv_natural_fst {S T : LightProfinite.{0}} (f : S ⟶ T)
    (U : LightProfinite.{0}) :
    (Work.DISC.freeTensorIso S U).inv ≫ (Work.ATOM.zmap f ▷ Work.DISC.zfree U) =
      Work.DISC.zfreeFunctor.map (f ▷ U) ≫ (Work.DISC.freeTensorIso T U).inv := by
  have h := freeTensorIso_natural_fst f U
  have h2 : (Work.ATOM.zmap f ▷ Work.DISC.zfree U) =
      (Work.DISC.freeTensorIso S U).hom ≫ Work.DISC.zfreeFunctor.map (f ▷ U) ≫
        (Work.DISC.freeTensorIso T U).inv := by
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Currying of locally constant functions commutes with restriction in the *free* variable. -/
theorem lcCurryEquiv_comap_fst (M : ModuleCat ℤ) {S T : LightProfinite.{0}} (f : S ⟶ T)
    (U : LightProfinite.{0}) (ψ : LocallyConstant (↥T.toTop × ↥U.toTop) ↥M) :
    lcCurryEquiv S U M (LocallyConstant.comap (prodMapFst f U) ψ)
      = LocallyConstant.map (LocallyConstant.comapₗ ℤ f.hom.hom) (lcCurryEquiv T U M ψ) := by
  ext u s
  simp [lcCurryEquiv_apply, LocallyConstant.coe_comap_apply, prodMapFst]

/-! ## Naturality of `sdPhi` and of `sdComp` in the free variable -/

set_option backward.isDefEq.respectTransparency false

/-- **Naturality of `sdPhi` in the free variable.**  Restricting a morphism
`ℤ[U] ⟶ (ℤ[S] ⟹ ΔM)` along `pre (zmap f)` (`f : S ⟶ T`) corresponds, under `sdPhi`, to
restricting a locally constant function on `T × U` along `f × id`. -/
theorem sdPhi_pre (M : ModuleCat ℤ) {S T : LightProfinite.{0}} (f : S ⟶ T)
    (U : LightProfinite.{0})
    (a : Work.DISC.zfree U ⟶ (CategoryTheory.ihom (Work.DISC.zfree T)).obj (Work.DISC.lcDisc M)) :
    Work.DISC.sdPhi M S U (a ≫ (MonoidalClosed.pre (Work.ATOM.zmap f)).app (Work.DISC.lcDisc M))
      = LocallyConstant.comap (prodMapFst f U) (Work.DISC.sdPhi M T U a) := by
  rw [Work.DISC.sdPhi_apply, Work.DISC.sdPhi_apply, MonoidalClosed.uncurry_pre_app]
  have h1 : (Work.DISC.freeTensorIso S U).inv ≫ (Work.ATOM.zmap f ▷ Work.DISC.zfree U) ≫
        MonoidalClosed.uncurry a =
      Work.DISC.zfreeFunctor.map (f ▷ U) ≫
        ((Work.DISC.freeTensorIso T U).inv ≫ MonoidalClosed.uncurry a) := by
    rw [← Category.assoc, freeTensorIso_inv_natural_fst, Category.assoc]
  rw [h1, Work.DISC.homFreeEquiv_naturality, Work.DISC.lcDisc_map]
  congr 1

/-- **Naturality of `sdComp` in the free variable**: the sectionwise comparison `sd ℤ[T] ≅ Cdisc T`
is compatible with `pre (zmap f)` and with `LocallyConstant.comap f`. -/
theorem sdComp_pre (S T : LightProfinite.{0}) (f : S ⟶ T) (M : ModuleCat ℤ)
    (U : LightProfinite.{0})
    (a : Work.DISC.zfree U ⟶ (CategoryTheory.ihom (Work.DISC.zfree T)).obj (Work.DISC.lcDisc M)) :
    sdComp S M U (Work.DISC.homFreeEquiv U _
        (a ≫ (MonoidalClosed.pre (Work.ATOM.zmap f)).app (Work.DISC.lcDisc M)))
      = LocallyConstant.map (LocallyConstant.comapₗ ℤ f.hom.hom)
          (sdComp T M U (Work.DISC.homFreeEquiv U _ a)) := by
  rw [sdComp_homFreeEquiv, sdPhi_pre M f U a, lcCurryEquiv_comap_fst M f U, ← sdComp_homFreeEquiv]

/-! ## Extensionality on free modules -/

/-- Two morphisms of light condensed abelian groups with the same domain agree if their
`homFreeEquiv`-values on `a : ℤ[U] ⟶ A` agree for all light profinite `U`. -/
theorem ext_of_homFreeEquiv {A B : LightCondAb} (h1 h2 : A ⟶ B)
    (H : ∀ (U : LightProfinite.{0}) (a : Work.DISC.zfree U ⟶ A),
      Work.DISC.homFreeEquiv U B (a ≫ h1) = Work.DISC.homFreeEquiv U B (a ≫ h2)) :
    h1 = h2 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  obtain ⟨V⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have e1 := homFreeEquiv_comp V ((Work.DISC.homFreeEquiv V A).symm x) h1
  rw [Equiv.apply_symm_apply] at e1
  have e2 := homFreeEquiv_comp V ((Work.DISC.homFreeEquiv V A).symm x) h2
  rw [Equiv.apply_symm_apply] at e2
  rw [← e1, ← e2]
  exact H V _

/-! ## The main theorem -/

theorem sdBridge_natural (S T : LightProfinite.{0}) (f : S ⟶ T) :
    (Work.ANALYTIC.CechPt.sdBridge T).hom ≫
      (LightCondMod.LocallyConstant.functor ℤ).map
        (ModuleCat.ofHom (LocallyConstant.comapₗ ℤ f.hom.hom))
      = (MonoidalClosed.pre (Work.ATOM.zmap f)).app (𝟙_ LightCondAb) ≫
        (Work.ANALYTIC.CechPt.sdBridge S).hom := by
  apply ext_of_homFreeEquiv
  intro U a
  rw [show a ≫ ((sdBridge T).hom ≫ (LightCondMod.LocallyConstant.functor ℤ).map
        (ModuleCat.ofHom (LocallyConstant.comapₗ ℤ f.hom.hom))) =
      (a ≫ (sdBridge T).hom) ≫ (LightCondMod.LocallyConstant.functor ℤ).map
        (ModuleCat.ofHom (LocallyConstant.comapₗ ℤ f.hom.hom)) from
    (Category.assoc a (sdBridge T).hom _).symm]
  rw [lcMap_homFreeEquiv f U (a ≫ (sdBridge T).hom)]
  rw [show a ≫ (sdBridge T).hom =
      a ≫ ((CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv ≫
        sdIsoHom T (ModuleCat.of ℤ ℤ)) from by rw [sdBridge_hom T]]
  rw [show a ≫ ((CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv ≫
        sdIsoHom T (ModuleCat.of ℤ ℤ)) =
      (a ≫ (CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv) ≫
        sdIsoHom T (ModuleCat.of ℤ ℤ) from
    (Category.assoc a ((CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv) _).symm]
  rw [sdIsoHom_homFreeEquiv T (ModuleCat.of ℤ ℤ) U
    (a ≫ (CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv)]
  have hpc : (MonoidalClosed.pre (Work.ATOM.zmap f)).app (𝟙_ LightCondAb) ≫
      (CategoryTheory.ihom (Work.DISC.zfree S)).map lcDiscIntIso.inv =
      (CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv ≫
        (MonoidalClosed.pre (Work.ATOM.zmap f)).app (Work.DISC.lcDisc (ModuleCat.of ℤ ℤ)) :=
    MonoidalClosed.pre_comm_ihom_map (Work.ATOM.zmap f) lcDiscIntIso.inv
  rw [show a ≫ ((MonoidalClosed.pre (Work.ATOM.zmap f)).app (𝟙_ LightCondAb) ≫
        (sdBridge S).hom) =
      ((a ≫ (MonoidalClosed.pre (Work.ATOM.zmap f)).app (𝟙_ LightCondAb)) ≫
        (CategoryTheory.ihom (Work.DISC.zfree S)).map lcDiscIntIso.inv) ≫
          sdIsoHom S (ModuleCat.of ℤ ℤ) from by
    rw [sdBridge_hom S]
    simp only [Category.assoc]]
  rw [show ((a ≫ (MonoidalClosed.pre (Work.ATOM.zmap f)).app (𝟙_ LightCondAb)) ≫
        (CategoryTheory.ihom (Work.DISC.zfree S)).map lcDiscIntIso.inv) ≫
          sdIsoHom S (ModuleCat.of ℤ ℤ) =
      ((a ≫ (CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv) ≫
        (MonoidalClosed.pre (Work.ATOM.zmap f)).app (Work.DISC.lcDisc (ModuleCat.of ℤ ℤ))) ≫
          sdIsoHom S (ModuleCat.of ℤ ℤ) from by
    calc ((a ≫ (MonoidalClosed.pre (Work.ATOM.zmap f)).app (𝟙_ LightCondAb)) ≫
          (CategoryTheory.ihom (Work.DISC.zfree S)).map lcDiscIntIso.inv) ≫
            sdIsoHom S (ModuleCat.of ℤ ℤ)
        = (a ≫ ((MonoidalClosed.pre (Work.ATOM.zmap f)).app (𝟙_ LightCondAb) ≫
            (CategoryTheory.ihom (Work.DISC.zfree S)).map lcDiscIntIso.inv)) ≫
              sdIsoHom S (ModuleCat.of ℤ ℤ) := by
          rw [Category.assoc a ((MonoidalClosed.pre (Work.ATOM.zmap f)).app (𝟙_ LightCondAb))
            ((CategoryTheory.ihom (Work.DISC.zfree S)).map lcDiscIntIso.inv)]
      _ = (a ≫ ((CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv ≫
            (MonoidalClosed.pre (Work.ATOM.zmap f)).app (Work.DISC.lcDisc (ModuleCat.of ℤ ℤ)))) ≫
              sdIsoHom S (ModuleCat.of ℤ ℤ) := by rw [hpc]
      _ = ((a ≫ (CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv) ≫
            (MonoidalClosed.pre (Work.ATOM.zmap f)).app (Work.DISC.lcDisc (ModuleCat.of ℤ ℤ))) ≫
              sdIsoHom S (ModuleCat.of ℤ ℤ) := by
          rw [← Category.assoc a ((CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv)
            ((MonoidalClosed.pre (Work.ATOM.zmap f)).app
              (Work.DISC.lcDisc (ModuleCat.of ℤ ℤ)))]]
  rw [sdIsoHom_homFreeEquiv S (ModuleCat.of ℤ ℤ) U
    ((a ≫ (CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv) ≫
      (MonoidalClosed.pre (Work.ATOM.zmap f)).app (Work.DISC.lcDisc (ModuleCat.of ℤ ℤ)))]
  rw [sdComp_pre S T f (ModuleCat.of ℤ ℤ) U
    (a ≫ (CategoryTheory.ihom (Work.DISC.zfree T)).map lcDiscIntIso.inv)]

end Work.ANALYTIC.CechPt
