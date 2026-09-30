import Mathlib
import Submission.Work.AbVar.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped CategoryTheory.MonObj

namespace Work.AbVar.Hom

open CategoryTheory in
theorem sectionLeft_homObstruction {k : Type*} [Field k] {G H : Work.AbVar.Sch k}
    [GrpObj G] [GrpObj H] (g : G ⟶ H)
    (hg : MonObj.one (X := G) ≫ g = MonObj.one (X := H)) :
    Work.AbVar.sectionLeft G G (MonObj.one (X := G)) ≫ Work.AbVar.homObstruction g =
      SemiCartesianMonoidalCategory.toUnit G ≫ MonObj.one (X := H) := by
  rw [Work.AbVar.homObstruction]
  simp only [MonObj.comp_mul, GrpObj.comp_inv]
  have hμ : Work.AbVar.sectionLeft G G (MonObj.one (X := G)) ≫ μ[G] = 𝟙 G :=
    MonObj.lift_comp_one_right (𝟙 G) (SemiCartesianMonoidalCategory.toUnit G)
  rw [← Category.assoc, hμ, Category.id_comp]
  rw [← Category.assoc, Work.AbVar.sectionLeft_fst, Category.id_comp]
  rw [← Category.assoc, Work.AbVar.sectionLeft_snd, Category.assoc, hg]
  rw [show (SemiCartesianMonoidalCategory.toUnit G ≫ MonObj.one (X := H) : G ⟶ H) = 1 from rfl,
      inv_one, mul_inv_cancel, mul_one]

end Work.AbVar.Hom
