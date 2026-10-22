import Mathlib
import Submission.Work.ANALYTIC.CechPt.DdZfAux

/-!
# `lamHat T (lamJ T n) = fCyl T n`

The `n`-th Haar functional `lamJ T n` of `ℤ[T]` (the dual element attached to the cylinder
`fCyl T n`) is sent by `lamHat T = homFreeEquiv T LCZ (- ≫ ZisoLCZ.hom)` to that same cylinder.

Concretely, `lamJ T n = kappaLCZ T n ≫ ZisoLCZ.inv`, so after cancelling the isomorphism
`ZisoLCZ` the goal becomes `LCZcoe T (homFreeEquiv T LCZ (kappaLCZ T n)) = fCyl T n`, and this is
checked pointwise at `t : ↥T`: naturality of `homFreeEquiv` along `ptAt t` turns the value at `t`
into the value at the point of `homFreeEquiv` of `zmap (ptAt t) ≫ kappaLCZ T n`, which is
`(fCyl T n t) • oneLCZ` by `kappaLCZ_pt`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC.CechPt

/-- **Cancellation of `ZisoLCZ` in `lamJ`**: composing the `n`-th Haar functional with the
identification `ZisoLCZ.hom : Z ≅ LCZ` recovers `kappaLCZ T n`. -/
theorem lamJ_comp_ZisoLCZ_hom (T : LightProfinite.{0}) [Infinite T] (n : ℕ) :
    lamJ T n ≫ (Work.ANALYTIC.ZisoLCZ.hom : (𝟙_ LightCondAb) ⟶ Work.ATOM.ZS.Unred.LCZ) =
      (Work.ANALYTIC.kappaLCZ T n : Work.ATOM.zfree T ⟶ Work.ATOM.ZS.Unred.LCZ) := by
  have hcompZ : (lamJ T n : Work.ATOM.zfree T ⟶ Work.ANALYTIC.Z) ≫
      Work.ANALYTIC.ZisoLCZ.hom
      = (Work.ANALYTIC.kappaLCZ T n : Work.ATOM.zfree T ⟶ Work.ATOM.ZS.Unred.LCZ) := by
    show ((Work.ANALYTIC.kappaLCZ T n :
          Work.ATOM.zfree T ⟶ Work.ATOM.ZS.Unred.LCZ) ≫ Work.ANALYTIC.ZisoLCZ.inv) ≫
        Work.ANALYTIC.ZisoLCZ.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hcompZ

theorem lamHat_lamJ (T : LightProfinite.{0}) [Infinite T] (n : ℕ) :
    Work.ANALYTIC.CechPt.lamHat T (Work.ANALYTIC.CechPt.lamJ T n) =
      Work.ANALYTIC.Haar.fCyl T n := by
  have hcomp : lamJ T n ≫
      (Work.ANALYTIC.ZisoLCZ.hom : (𝟙_ LightCondAb) ⟶ Work.ATOM.ZS.Unred.LCZ)
      = (Work.ANALYTIC.kappaLCZ T n : Work.ATOM.zfree T ⟶ Work.ATOM.ZS.Unred.LCZ) :=
    lamJ_comp_ZisoLCZ_hom T n
  show Work.ANALYTIC.LCZcoe T (Work.ATOM.homFreeEquiv T Work.ATOM.ZS.Unred.LCZ
      (lamJ T n ≫ Work.ANALYTIC.ZisoLCZ.hom)) = Work.ANALYTIC.Haar.fCyl T n
  rw [hcomp]
  apply LocallyConstant.ext
  intro t
  rw [Work.ANALYTIC.LCZcoe_map_apply]
  rw [← Work.ATOM.homFreeEquiv_zmap (Work.ATOM.ptAt t) Work.ATOM.ZS.Unred.LCZ
     (Work.ANALYTIC.kappaLCZ T n)]
  rw [Work.ANALYTIC.homFreeEquiv_kappaLCZ_pt]
  rw [Work.ANALYTIC.LCZcoe_smul_oneLCZ_val]

end Work.ANALYTIC.CechPt
