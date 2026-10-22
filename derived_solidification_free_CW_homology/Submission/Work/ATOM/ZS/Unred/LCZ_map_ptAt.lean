import Mathlib
import Submission.Work.ATOM.ZS.Unred.LCZ

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed
open Opposite

namespace Work.ATOM.ZS.Unred

/-- The section map of `LCZ` along a point map is given by pullback of locally constant functions
along the underlying continuous map (this is `functorToPresheaves_obj_map`). -/
theorem LCZ_obj_map (T : LightProfinite.{0}) (g : Work.ATOM.pt ⟶ T) :
    LCZ.obj.map g.op =
      ModuleCat.ofHom (LocallyConstant.comapₗ ℤ (TopCat.Hom.hom g.hom)) := by
  change ((LightCondMod.LocallyConstant.functorToPresheaves ℤ).obj (ModuleCat.of ℤ ℤ)).map g.op = _
  rw [CompHausLike.LocallyConstantModule.functorToPresheaves_obj_map]

theorem LCZ_map_ptAt (T : LightProfinite.{0}) (t : ↥T) (f : LocallyConstant ↥T.toTop ↥(ModuleCat.of ℤ ℤ)) : (Work.ATOM.ZS.Unred.LCZ.obj.map (Work.ATOM.ptAt t).op) f = (f t) • Work.ATOM.ZS.Unred.oneLCZ := by
  change (LocallyConstant.comapₗ ℤ (TopCat.Hom.hom (Work.ATOM.ptAt t).hom)) f =
    (f t) • LocallyConstant.const (↥Work.ATOM.pt.toTop) (1 : ℤ)
  apply LocallyConstant.ext
  intro x
  simp only [LocallyConstant.comapₗ, LocallyConstant.smul_apply, LocallyConstant.coe_const]
  simp
  rfl

end Work.ATOM.ZS.Unred
