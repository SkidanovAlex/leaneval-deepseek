import Mathlib
import Submission.Work.ANALYTIC.CechPt.DdZfAux
import Submission.Work.ANALYTIC.CechPt.homFreeEquiv_unitIso_inv

/-!
# `lamHat T (lamInf T) = 1`

The dual element `lamInf T = aug T ≫ unitIso.inv = zmap (toPt T) ≫ unitIso.inv` is the functional
`ℤ[T] ⟶ 𝟙` corresponding to the constant function `1`; the goal is that its image under the
"locally constant function attached to a functional" map `lamHat T` is the constant function `1`.

The proof has two ingredients.

* A reduction: `lamInf T = zmap (toPt T) ≫ unitIso.inv`, so by naturality of `homFreeEquiv` in the
  light profinite set (`Work.ATOM.homFreeEquiv_naturality`) it suffices to know the element
  `homFreeEquiv 𝟙 (unitIso.inv ≫ ZisoLCZ.hom) ∈ LCZ(∗)`; `lamHat T (lamInf T)` is then the
  pullback of that element along the constant map `T ⟶ ∗`, i.e. the corresponding constant
  function (`LCZ_map_toPt_oneLCZ`).
* The computation of that element: it is `oneLCZ` (= the constant function `1`).  Writing
  `dU := (discreteUnderlyingAdj ℤ).unit.app ℤ` for the unit of the constant-sheaf adjunction at
  `ℤ`, the element `dU 1 ∈ Z(∗)` is carried to `oneLCZ` by the section map of `ZisoLCZ`
  (`ZisoLCZ_hom_unitConstSheaf`, a consequence of `LCZ_unit_eq_auxHom`); hence it suffices to
  identify the two canonical generators `homFreeEquiv 𝟙 unitIso.inv = dU 1` of `Z(∗)`.

The second item (`homFreeEquiv_unitIso_inv`) is a coherence statement about the canonical
trivialisations `𝟙 ≅ ℤ[∗]` (`unitIso`, the monoidal `ε`-isomorphism of `free ℤ`) and
`𝟙 ≅ C(∗,ℤ) = LCZ` (`ZisoLCZ`/`lcDiscIntIso`); it is isolated as a separate lemma.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite

noncomputable section

namespace Work.ANALYTIC.CechPt

/-- The unit of the constant-sheaf adjunction `(discrete ℤ) ⊣ underlying` at `ℤ`, as an element of
`Z(∗) = 𝟙(∗)`.  This is the canonical generator of the sections of the constant sheaf `ℤ` at a
point. -/
noncomputable def unitConstSheaf : ↥(Work.ANALYTIC.Z.obj.obj (op Work.ATOM.pt)) :=
  (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ) (1 : ℤ)

/-- **`ZisoLCZ` carries the generator `unitConstSheaf` to `oneLCZ`.**  This is the formula
`LCZ_unit_eq_auxHom` for the unit of the adjunction `functor ℤ ⊣ underlying`
(`LCZauxHom ℤ = (discreteUnderlyingAdj ℤ).unit.app ℤ ≫ (underlying ℤ).map ZisoLCZ.hom`), together
with `LCZ_unit_const`, which says that this unit sends `1` to the constant function `1`. -/
theorem ZisoLCZ_hom_unitConstSheaf :
    (ConcreteCategory.hom (Work.ANALYTIC.ZisoLCZ.hom.hom.app (op Work.ATOM.pt))) unitConstSheaf
      = Work.ATOM.ZS.Unred.oneLCZ := by
  have h1 : Work.ATOM.ZS.Unred.LCZauxHom (ModuleCat.of ℤ ℤ)
      = (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)).unit.app (ModuleCat.of ℤ ℤ)
        ≫ (LightCondensed.underlying (ModuleCat ℤ)).map (Work.ANALYTIC.ZisoLCZ.hom) := by
    rw [← Work.ATOM.ZS.Unred.LCZ_unit_eq_auxHom]
    exact Work.ATOM.ZS.Unred.ofNatIsoLeft_unit_app
      (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ))
      ((LightCondMod.LocallyConstant.functorIsoDiscrete ℤ).symm) (ModuleCat.of ℤ ℤ)
  have h2 : (ConcreteCategory.hom (Work.ATOM.ZS.Unred.LCZauxHom (ModuleCat.of ℤ ℤ))) (1 : ℤ)
      = (ConcreteCategory.hom (Work.ANALYTIC.ZisoLCZ.hom.hom.app (op Work.ATOM.pt)))
          unitConstSheaf := by
    rw [h1]
    rfl
  rw [← h2, ← Work.ATOM.ZS.Unred.LCZ_unit_eq_auxHom]
  exact Work.ATOM.ZS.Unred.LCZ_unit_const (ModuleCat.of ℤ ℤ) 1

/-- The identification `ZisoLCZ.hom = lcDiscIntIso.inv`, with the type written so that the
composite with `Work.ATOM.unitIso.inv` elaborates without transparency issues. -/
theorem ZisoLCZ_hom_eq_lcDiscIntIso_inv :
    Work.ANALYTIC.ZisoLCZ.hom
      = (Work.ANALYTIC.CechPt.lcDiscIntIso.inv :
          (𝟙_ LightCondAb) ⟶ Work.ATOM.ZS.Unred.LCZ) :=
  (Work.ANALYTIC.CechPt.lcDiscIntIso_inv_eq_ZisoLCZ_hom).symm

/-- Given the coherence `homFreeEquiv 𝟙 unitIso.inv = dU 1`, the element of `LCZ(∗)` attached to
`unitIso.inv ≫ ZisoLCZ.hom` is the constant function `1`. -/
theorem homFreeEquiv_comp_lcDiscIntIso_inv
    (h : Work.ATOM.homFreeEquiv Work.ATOM.pt (𝟙_ LightCondAb) Work.ATOM.unitIso.inv
      = unitConstSheaf) :
    Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
      (CategoryTheory.CategoryStruct.comp Work.ATOM.unitIso.inv
        Work.ANALYTIC.CechPt.lcDiscIntIso.inv) = Work.ATOM.ZS.Unred.oneLCZ := by
  rw [Work.ATOM.homFreeEquiv_naturality_target (S := Work.ATOM.pt)
    (h := Work.ANALYTIC.CechPt.lcDiscIntIso.inv) (g := Work.ATOM.unitIso.inv)]
  rw [h]
  exact ZisoLCZ_hom_unitConstSheaf

/-- The element of `LCZ(T)` obtained by pulling back `oneLCZ` along the constant map `T ⟶ ∗` is
the constant function `1`. -/
theorem LCZ_map_toPt_oneLCZ (T : LightProfinite.{0}) :
    LCZcoe T (Work.ATOM.ZS.Unred.LCZ.obj.map (Work.ATOM.toPt T).op
        Work.ATOM.ZS.Unred.oneLCZ) = (1 : Haar.LC T) := by
  rw [show Work.ATOM.ZS.Unred.LCZ.obj.map (Work.ATOM.toPt T).op Work.ATOM.ZS.Unred.oneLCZ
      = LocallyConstant.comap (TopCat.Hom.hom (Work.ATOM.toPt T).hom)
          Work.ATOM.ZS.Unred.oneLCZ from rfl]
  show LocallyConstant.comap (TopCat.Hom.hom (Work.ATOM.toPt T).hom)
      (LocallyConstant.const ↥(Work.ATOM.pt.toTop) (1 : ℤ)) = (1 : LocallyConstant ↥T.toTop ℤ)
  apply LocallyConstant.ext
  intro x
  rw [LocallyConstant.coe_comap_apply]
  rfl

/-- **The main computation, given the coherence `homFreeEquiv 𝟙 unitIso.inv = dU 1`.**
For the functional `lamInf T` corresponding to the constant function `1`, the locally constant
function `lamHat T (lamInf T)` is the constant function `1`. -/
theorem lamHat_lamInf_of (T : LightProfinite.{0})
    (h : Work.ATOM.homFreeEquiv Work.ATOM.pt (𝟙_ LightCondAb) Work.ATOM.unitIso.inv
      = unitConstSheaf) :
    lamHat T (lamInf T) = 1 := by
  have hkey := homFreeEquiv_comp_lcDiscIntIso_inv h
  have hinf : Work.ANALYTIC.CechPt.lamInf T
      = CategoryTheory.CategoryStruct.comp (Work.ATOM.zmap (Work.ATOM.toPt T))
          Work.ATOM.unitIso.inv := rfl
  have hF : Work.ATOM.homFreeEquiv T Work.ATOM.ZS.Unred.LCZ
      (CategoryTheory.CategoryStruct.comp (Work.ANALYTIC.CechPt.lamInf T)
        (Work.ANALYTIC.CechPt.lcDiscIntIso.inv :
          (𝟙_ LightCondAb) ⟶ Work.ATOM.ZS.Unred.LCZ))
      = Work.ATOM.ZS.Unred.LCZ.obj.map (Work.ATOM.toPt T).op Work.ATOM.ZS.Unred.oneLCZ := by
    rw [hinf, Category.assoc]
    rw [Work.ATOM.homFreeEquiv_naturality (Work.ATOM.toPt T)
      (CategoryTheory.CategoryStruct.comp Work.ATOM.unitIso.inv
        Work.ANALYTIC.CechPt.lcDiscIntIso.inv)]
    rw [hkey]
  rw [show Work.ANALYTIC.CechPt.lamHat T (Work.ANALYTIC.CechPt.lamInf T)
      = LCZcoe T (Work.ATOM.homFreeEquiv T Work.ATOM.ZS.Unred.LCZ
          (CategoryTheory.CategoryStruct.comp (Work.ANALYTIC.CechPt.lamInf T)
            Work.ANALYTIC.ZisoLCZ.hom)) from rfl]
  rw [show (Work.ANALYTIC.ZisoLCZ.hom :
      Work.ANALYTIC.Z ⟶ Work.ATOM.ZS.Unred.LCZ)
      = (Work.ANALYTIC.CechPt.lcDiscIntIso.inv :
          (𝟙_ LightCondAb) ⟶ Work.ATOM.ZS.Unred.LCZ) from
    Work.ANALYTIC.CechPt.ZisoLCZ_hom_eq_lcDiscIntIso_inv]
  rw [hF]
  exact LCZ_map_toPt_oneLCZ T

theorem lamHat_lamInf (T : LightProfinite.{0}) [Infinite T] :
    Work.ANALYTIC.CechPt.lamHat T (Work.ANALYTIC.CechPt.lamInf T) = 1 :=
  lamHat_lamInf_of T homFreeEquiv_unitIso_inv

end Work.ANALYTIC.CechPt
