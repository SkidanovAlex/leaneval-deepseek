import Mathlib
import Submission.Work.ANALYTIC.CechPt.DdZfAux
import Submission.Work.ANALYTIC.CechPt.sdBridge_natural

/-!
# `gamma_phiT`: the value of the bridge `sd ℤ[T] ≅ Cdisc T` at `phiOf`

For a light profinite set `T` and a functional `lam : ℤ[T] ⟶ 𝟙`, the global section
`phiOf (zf T) lam : 𝟙 ⟶ sd (ℤ[T])` of the single dual corresponds, under the canonical
isomorphism `phiT T : sd (ℤ[T]) ≅ Cdisc T`, to the locally constant function `lamHat T lam`:

`toPointEquiv (Cdisc T) (phiOf (zf T) lam ≫ (phiT T).hom) = LocallyConstant.const _ (lamHat T lam)`.

The proof is the explicit computation described in `DdZfAux.lean`:

* `toPointEquiv` is `homFreeEquiv` at the point, applied to `unitIso.inv`;
* `curry_natural_right` turns `phiOf ≫ ihom.map lcDiscIntIso.inv` into the currying of
  `h = (ρ_ ℤ[T]) ≫ lam ≫ lcDiscIntIso.inv`;
* naturality of `homFreeEquiv` in the target identifies the section map of `sdIsoHom` at the
  point with `sdComp` and then with `lcCurryEquiv ∘ sdPhi`;
* `sdPhi` is evaluated by uncurrying (`uncurry_curry`), by the oplax unitality of the monoidal
  functor `zfree` (which computes `(ℤ[T] ⊗ ℤ[pt])⁻¹ ≫ (ℤ[T] ◁ ε⁻¹) = zmap ρ ≫ ρ⁻¹`) and by
  naturality of `homFreeEquiv` in the light profinite set;
* the last step is the unitor computation `lcCurryEquiv_comap_unitor`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Work.ANALYTIC.CechPt

/-! ## Sectionwise lemmas for the bridge -/

/-- **Sections of a composite**: applying the section map of `h : A ⟶ B` at `U` to the section of
`A` corresponding to `a : ℤ[U] ⟶ A` is the same as evaluating `homFreeEquiv` on `a ≫ h`. -/
theorem homFreeEquiv_comp' (U : LightProfinite.{0}) {A B : LightCondAb}
    (a : Work.DISC.zfree U ⟶ A) (h : A ⟶ B) :
    Work.DISC.homFreeEquiv U B (a ≫ h) =
      ModuleCat.Hom.hom (h.hom.app (op U)) (Work.DISC.homFreeEquiv U A a) := rfl

/-- `sdIsoHom` is the sectionwise comparison `sdComp`. -/
theorem sdIsoHom_app_apply (T : LightProfinite.{0}) (M : ModuleCat ℤ) (U : LightProfinite.{0})
    (y : ↥(((CategoryTheory.ihom (Work.DISC.zfree T)).obj (Work.DISC.lcDisc M)).obj.obj
      (op U))) :
    ModuleCat.Hom.hom ((sdIsoHom T M).hom.app (op U)) y = sdComp T M U y := by
  have h : (sdIsoHom T M).hom = sdNatTrans T M := by
    have hF : (sheafToPresheaf cechTop (ModuleCat ℤ)).map (sdIsoHom T M) =
        (sdIsoHom T M).hom := rfl
    rw [← hF]
    exact Functor.map_preimage _ _
  rw [h]
  rfl

/-- `sdComp` evaluated on a morphism out of `ℤ[U]` is `lcCurryEquiv ∘ sdPhi`. -/
theorem sdComp_homFreeEquiv_apply (T : LightProfinite.{0}) (M : ModuleCat ℤ)
    (U : LightProfinite.{0})
    (g : Work.DISC.zfree U ⟶ (CategoryTheory.ihom (Work.DISC.zfree T)).obj
      (Work.DISC.lcDisc M)) :
    sdComp T M U (Work.DISC.homFreeEquiv U _ g) =
      lcCurryEquiv T U M (Work.DISC.sdPhi M T U g) := by
  rw [sdComp_apply, ← homFreeLinearEquiv_apply, LinearEquiv.symm_apply_apply, sdPhiLin_apply]

/-! ## The currying computation -/

/-- `phiOf X lam` followed by the transport `ihom X` of `lcDiscIntIso.inv` is the currying of
`(ρ_ X) ≫ lam ≫ lcDiscIntIso.inv`. -/
theorem phiOf_comp_ihom_map (T : LightProfinite.{0}) (lam : zf T ⟶ 𝟙_ LightCondAb) :
    phiOf (zf T) lam ≫ (ihom (zf T)).map lcDiscIntIso.inv =
      MonoidalClosed.curry (((ρ_ (zf T)).hom ≫ lam) ≫ lcDiscIntIso.inv) := by
  rw [phiOf, ← MonoidalClosed.curry_natural_right]

/-- Uncurrying the composite `unitIso.inv ≫ curry h` (where `unitIso.inv : ℤ[pt] ⟶ 𝟙`) gives
`(ℤ[T] ◁ unitIso.inv) ≫ h`. -/
theorem uncurry_unitIso_inv_curry (T : LightProfinite.{0})
    (h : zf T ⊗ 𝟙_ LightCondAb ⟶ Work.DISC.lcDisc (ModuleCat.of ℤ ℤ)) :
    MonoidalClosed.uncurry (Work.ATOM.unitIso.inv ≫ MonoidalClosed.curry h) =
      (zf T ◁ Work.ATOM.unitIso.inv) ≫ h := by
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]

/-! ## Oplax unitality of the monoidal functor `zfree` -/

/-- **The unitality coherence.**  For the monoidal functor `zfree = ℤ[-]`, the inverse tensorator
`(ℤ[T] ⊗ ℤ[pt])⁻¹` followed by `ℤ[T] ◁ ε⁻¹` (where `ε⁻¹ = unitIso.inv = η` is the oplax unit) is
`zmap (ρ_T) ≫ (ρ_{ℤ[T]})⁻¹`. -/
theorem freeTensorIso_inv_whisker_unitIso_inv (T : LightProfinite.{0}) :
    (Work.DISC.freeTensorIso T Work.ATOM.Point).inv ≫ (zf T ◁ Work.ATOM.unitIso.inv) =
      Work.ATOM.zmap ((ρ_ T).hom) ≫ (ρ_ (zf T)).inv := by
  have h2 : Functor.OplaxMonoidal.δ Work.DISC.zfreeFunctor T (𝟙_ LightProfinite) ≫
      (Work.DISC.zfreeFunctor.obj T ◁ Functor.OplaxMonoidal.η Work.DISC.zfreeFunctor) ≫
        (ρ_ (Work.DISC.zfreeFunctor.obj T)).hom = Work.ATOM.zmap ((ρ_ T).hom) := by
    rw [Functor.OplaxMonoidal.right_unitality_hom]
  show Functor.OplaxMonoidal.δ Work.DISC.zfreeFunctor T (𝟙_ LightProfinite) ≫
      (Work.DISC.zfreeFunctor.obj T ◁ Functor.OplaxMonoidal.η Work.DISC.zfreeFunctor) =
    Work.ATOM.zmap ((ρ_ T).hom) ≫ (ρ_ (Work.DISC.zfreeFunctor.obj T)).inv
  rw [← h2]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-! ## The unitor computation at the point -/

/-- Evaluating the currying `lcCurryEquiv` of a locally constant function pulled back along the
right unitor `ρ_T : T ⊗ pt ⟶ T` at the point gives the constant function. -/
theorem lcCurryEquiv_comap_unitor (T : LightProfinite.{0}) (ψ : Haar.LC T) :
    lcCurryEquiv T Work.ATOM.Point (ModuleCat.of ℤ ℤ)
        (LocallyConstant.comap ((ρ_ T).hom.hom.hom) ψ) =
      LocallyConstant.const ↥(Work.ATOM.Point.toTop) ψ := by
  apply LocallyConstant.ext
  intro t
  apply LocallyConstant.ext
  intro s
  show (LocallyConstant.comap (TopCat.Hom.hom (ρ_ T).hom.hom) ψ) (s, t) = ψ s
  rfl

/-! ## The section computation for `sdPhi` -/

/-- **The value of `sdPhi` on `unitIso.inv ≫ curry h`.** -/
theorem sdPhi_unitIso_inv_curry (T : LightProfinite.{0}) (lam : zf T ⟶ 𝟙_ LightCondAb) :
    Work.DISC.sdPhi (ModuleCat.of ℤ ℤ) T Work.ATOM.Point
        (Work.ATOM.unitIso.inv ≫ MonoidalClosed.curry
          (((ρ_ (zf T)).hom ≫ lam) ≫ lcDiscIntIso.inv)) =
      LocallyConstant.comap ((ρ_ T).hom.hom.hom)
        (Work.DISC.homFreeEquiv T (Work.DISC.lcDisc (ModuleCat.of ℤ ℤ))
          (lam ≫ lcDiscIntIso.inv)) := by
  let h : zf T ⊗ 𝟙_ LightCondAb ⟶ Work.DISC.lcDisc (ModuleCat.of ℤ ℤ) :=
    ((ρ_ (zf T)).hom ≫ lam) ≫ lcDiscIntIso.inv
  rw [Work.DISC.sdPhi_apply]
  rw [show MonoidalClosed.uncurry (Work.ATOM.unitIso.inv ≫ MonoidalClosed.curry h) =
      (zf T ◁ Work.ATOM.unitIso.inv) ≫ h from uncurry_unitIso_inv_curry T h]
  rw [show (Work.DISC.freeTensorIso T Work.ATOM.Point).inv ≫
        (zf T ◁ Work.ATOM.unitIso.inv) ≫ h =
      Work.ATOM.zmap ((ρ_ T).hom) ≫ (lam ≫ lcDiscIntIso.inv) from by
    calc (Work.DISC.freeTensorIso T Work.ATOM.Point).inv ≫
          (zf T ◁ Work.ATOM.unitIso.inv) ≫ h
        = ((Work.DISC.freeTensorIso T Work.ATOM.Point).inv ≫
            (zf T ◁ Work.ATOM.unitIso.inv)) ≫ h := (Category.assoc _ _ _).symm
      _ = (Work.ATOM.zmap ((ρ_ T).hom) ≫ (ρ_ (zf T)).inv) ≫ h := by
            rw [freeTensorIso_inv_whisker_unitIso_inv]
      _ = Work.ATOM.zmap ((ρ_ T).hom) ≫ (ρ_ (zf T)).inv ≫ h := Category.assoc _ _ _
      _ = Work.ATOM.zmap ((ρ_ T).hom) ≫ (lam ≫ lcDiscIntIso.inv) := by
            rw [show (ρ_ (zf T)).inv ≫ h = lam ≫ lcDiscIntIso.inv from by
              simp only [h, Category.assoc, Iso.inv_hom_id_assoc]]]
  rw [Work.DISC.homFreeEquiv_naturality, Work.DISC.lcDisc_map]

/-! ## The main theorem -/

/-- `gamma_phiT` for a functional with values in the unit. -/
theorem gamma_phiT_aux (T : LightProfinite.{0}) (lam : zf T ⟶ 𝟙_ LightCondAb) :
    Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc T)
        (CategoryTheory.CategoryStruct.comp (phiOf (zf T) lam) (phiT T).hom) =
      LocallyConstant.const ↥(Work.ATOM.pt.toTop) (lamHat T lam) := by
  rw [Work.ATOM.toPointEquiv_apply]
  have hcurry : phiOf (zf T) lam ≫ (phiT T).hom =
      MonoidalClosed.curry (((ρ_ (zf T)).hom ≫ lam) ≫ lcDiscIntIso.inv) ≫
        sdIsoHom T (ModuleCat.of ℤ ℤ) := by
    rw [phiT_hom, ← Category.assoc, phiOf_comp_ihom_map]
  rw [hcurry, ← Category.assoc]
  erw [Work.ANALYTIC.CechPt.homFreeEquiv_comp]
  erw [Work.ANALYTIC.CechPt.sdIsoHom_app]
  erw [Work.ANALYTIC.CechPt.sdComp_homFreeEquiv]
  rw [sdPhi_unitIso_inv_curry]
  rw [lcCurryEquiv_comap_unitor]
  rfl

theorem gamma_phiT (T : LightProfinite.{0}) (lam : Work.ANALYTIC.CechPt.zf T ⟶ Work.ANALYTIC.Z) :
    Work.ATOM.toPointEquiv (Work.ANALYTIC.Cdisc T)
        (CategoryTheory.CategoryStruct.comp
          (Work.ANALYTIC.CechPt.phiOf (Work.ANALYTIC.CechPt.zf T) lam)
          (Work.ANALYTIC.CechPt.phiT T).hom) =
      LocallyConstant.const ↥(Work.ATOM.pt.toTop)
        (Work.ANALYTIC.CechPt.lamHat T lam) :=
  gamma_phiT_aux T lam

end Work.ANALYTIC.CechPt
