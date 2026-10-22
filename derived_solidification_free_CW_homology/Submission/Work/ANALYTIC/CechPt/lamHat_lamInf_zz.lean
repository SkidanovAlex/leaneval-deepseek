import Mathlib
import Submission.Work.ANALYTIC.CechPt.DdZfAux
import Submission.Work.ANALYTIC.CechPt.LCZhom_eq_unit

/-!
# `lamHat T (lamInf T) = 1` for every light profinite `T`

The functional `lamInf T = aug T ≫ unitIso.inv = zmap (toPt T) ≫ unitIso.inv : ℤ[T] ⟶ ℤ` is the
dual element attached to the constant function `1 ∈ C(T,ℤ)`; this module proves that the locally
constant function `lamHat T (lamInf T)` attached to it is the constant function `1`, for *every*
light profinite set `T` (in particular with no infinitude hypothesis).

`lamHat` is by definition the composite

`Hom(ℤ[T], ℤ) --(- ≫ ZisoLCZ.hom)--> Hom(ℤ[T], LCZ) --homFreeEquiv T LCZ--> LCZ(T) = C(T,ℤ)`,

so the statement is the evaluation of the section of `LCZ` over `T` classified by the morphism
`lamInf T ≫ ZisoLCZ.hom`.

## The argument

* `lamInf T = zmap (toPt T) ≫ unitIso.inv`, so by naturality of `homFreeEquiv` in the light
  profinite set (`Work.ATOM.homFreeEquiv_zmap`) the section classified by
  `lamInf T ≫ ZisoLCZ.hom` is the restriction to `T` of the *point* section classified by
  `unitIso.inv ≫ lcDiscIntIso.inv`; both `ZisoLCZ.hom` and `lcDiscIntIso.inv` are (definitionally)
  the same morphism `𝟙 ⟶ LCZ`.
* The point section is the canonical generator `oneLCZ` of `LCZ(∗) = ℤ`: this is the isomorphism
  `LCZhom = (homFreeEquiv ∗ LCZ).symm oneLCZ` of `Work.ATOM.ZS.Unred.LCZ_iso`, identified with the
  composite `unitIso.inv ≫ lcDiscIntIso.inv` by `Work.ANALYTIC.CechPt.LCZhom_eq_unit`.
* Finally the restriction of `oneLCZ` to `T` along the terminal map `T ⟶ ∗` is the constant
  function `1` (`LCZ`'s restriction maps are pullbacks of locally constant functions).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite

noncomputable section

namespace Work.ANALYTIC.CechPt

/-! ## The sections of `LCZ` are pullbacks of locally constant functions -/

/-- The section map of the `LCZ`-model `S ↦ LocallyConstant S ℤ` of `ℤ` is the pullback of
locally constant functions along the underlying continuous map. -/
theorem LCZ_obj_map_zz {S T : LightProfinite.{0}} (f : S ⟶ T)
    (v : ↥(Work.ATOM.ZS.Unred.LCZ.obj.obj (Opposite.op T))) :
    (Work.ATOM.ZS.Unred.LCZ.obj.map f.op) v
      = (LocallyConstant.comap (TopCat.Hom.hom f.hom) v : LocallyConstant ↥S ℤ) := by
  change (LocallyConstant.comapₗ ℤ (TopCat.Hom.hom f.hom)) v
      = (LocallyConstant.comap (TopCat.Hom.hom f.hom) v : LocallyConstant ↥S ℤ)
  rfl

/-- The restriction of the canonical generator `oneLCZ` of `LCZ(∗)` along the terminal map
`T ⟶ ∗` is the constant function `1`. -/
theorem LCZ_map_toPt_oneLCZ_zz (T : LightProfinite.{0}) :
    (Work.ATOM.ZS.Unred.LCZ.obj.map (Work.ATOM.toPt T).op Work.ATOM.ZS.Unred.oneLCZ)
      = (1 : LocallyConstant ↥T ℤ) := by
  rw [show (Work.ATOM.ZS.Unred.LCZ.obj.map (Work.ATOM.toPt T).op Work.ATOM.ZS.Unred.oneLCZ)
      = (LocallyConstant.comap (TopCat.Hom.hom (Work.ATOM.toPt T).hom)
          Work.ATOM.ZS.Unred.oneLCZ : LocallyConstant ↥T ℤ) from
        LCZ_obj_map_zz (Work.ATOM.toPt T) Work.ATOM.ZS.Unred.oneLCZ]
  rw [Work.ATOM.ZS.Unred.oneLCZ]
  rw [show (LocallyConstant.comap (TopCat.Hom.hom (Work.ATOM.toPt T).hom)
      (LocallyConstant.const ↥Work.ATOM.pt.toTop (1 : ℤ)) : LocallyConstant ↥T ℤ)
      = LocallyConstant.const ↥T (1 : ℤ) from
        congr_fun (LocallyConstant.comap_const (TopCat.Hom.hom (Work.ATOM.toPt T).hom)
          PUnit.unit (fun _ => rfl)) _]
  rfl

/-! ## The point case -/

/-- **The point coherence.**  The isomorphism `LCZhom : ℤ[∗] ⟶ LCZ` of
`Work.ATOM.ZS.Unred.LCZ_iso` (carrying the canonical generator `e₁` to `oneLCZ`) is the composite
of `unitIso.inv : ℤ[∗] ⟶ 𝟙` with `lcDiscIntIso.inv : 𝟙 ⟶ LCZ`
(`Work.ANALYTIC.CechPt.LCZhom_eq_unit`).  Hence the section of `LCZ` over the point classified by
`unitIso.inv ≫ lcDiscIntIso.inv` is the canonical generator `oneLCZ`. -/
theorem homFreeEquiv_unitIso_inv_comp_zz :
    Work.ATOM.homFreeEquiv Work.ATOM.pt Work.ATOM.ZS.Unred.LCZ
        (Work.ATOM.unitIso.inv ≫ lcDiscIntIso.inv) = Work.ATOM.ZS.Unred.oneLCZ := by
  rw [← LCZhom_eq_unit]
  exact Work.ATOM.ZS.Unred.homFreeEquiv_LCZhom

/-! ## The main theorem -/

theorem lamHat_lamInf_zz (T : LightProfinite.{0}) :
    Work.ANALYTIC.CechPt.lamHat T (Work.ANALYTIC.CechPt.lamInf T) = 1 := by
  -- The section of `LCZ` over `T` classified by `lamInf T ≫ ZisoLCZ.hom` is the restriction of
  -- the point section classified by `unitIso.inv ≫ lcDiscIntIso.inv`.
  have hsection :
      Work.ATOM.homFreeEquiv T Work.ATOM.ZS.Unred.LCZ
          (lamInf T ≫ Work.ANALYTIC.ZisoLCZ.hom)
        = Work.ATOM.ZS.Unred.LCZ.obj.map (Work.ATOM.toPt T).op Work.ATOM.ZS.Unred.oneLCZ := by
    rw [← lcDiscIntIso_inv_eq_ZisoLCZ_hom]
    show Work.ATOM.homFreeEquiv T Work.ATOM.ZS.Unred.LCZ
        (Work.ATOM.zmap (Work.ATOM.toPt T) ≫ (Work.ATOM.unitIso.inv ≫ lcDiscIntIso.inv)) = _
    rw [Work.ATOM.homFreeEquiv_zmap]
    rw [homFreeEquiv_unitIso_inv_comp_zz]
  show Work.ANALYTIC.LCZcoe T
      (Work.ATOM.homFreeEquiv T Work.ATOM.ZS.Unred.LCZ
        (lamInf T ≫ Work.ANALYTIC.ZisoLCZ.hom)) = (1 : Haar.LC T)
  rw [hsection]
  exact LCZ_map_toPt_oneLCZ_zz T

end Work.ANALYTIC.CechPt
