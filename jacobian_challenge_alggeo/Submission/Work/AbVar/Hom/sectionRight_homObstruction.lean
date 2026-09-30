import Mathlib
import Submission.Work.AbVar.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.AbVar.Hom

open CategoryTheory
open scoped MonObj

variable {k : Type*} [Field k]

/-- The graph section `G ⟶ G ⊗ G`, `x ↦ (1, x)`, followed by the group law of `G` is the
identity: `(x, y) ↦ (1, x)` is a section of the projection onto the second factor. -/
lemma sectionRight_one_mul (G : Work.AbVar.Sch k) [GrpObj G] :
    Work.AbVar.sectionRight G G (MonObj.one (X := G)) ≫ (MonObj.mul (X := G)) = 𝟙 G :=
  MonObj.lift_comp_one_left (SemiCartesianMonoidalCategory.toUnit G) (𝟙 G)

variable {G H : Work.AbVar.Sch k} [GrpObj G] [GrpObj H]

open CategoryTheory in
theorem sectionRight_homObstruction {k : Type*} [Field k] {G H : Work.AbVar.Sch k}
    [GrpObj G] [GrpObj H] (g : G ⟶ H)
    (hg : MonObj.one (X := G) ≫ g = MonObj.one (X := H)) :
    Work.AbVar.sectionRight G G (MonObj.one (X := G)) ≫ Work.AbVar.homObstruction g =
      SemiCartesianMonoidalCategory.toUnit G ≫ MonObj.one (X := H) := by
  -- Evaluation of the three factors of the obstruction along the section `x ↦ (1, x)`.
  have hμ : Work.AbVar.sectionRight G G (MonObj.one (X := G)) ≫
      (MonObj.mul (X := G) ≫ g) = g := by
    rw [← Category.assoc, sectionRight_one_mul, Category.id_comp]
  have hf : Work.AbVar.sectionRight G G (MonObj.one (X := G)) ≫
      (SemiCartesianMonoidalCategory.fst G G ≫ g) =
      SemiCartesianMonoidalCategory.toUnit G ≫ MonObj.one (X := H) := by
    rw [← Category.assoc, Work.AbVar.sectionRight_fst, Category.assoc, hg]
  have hs : Work.AbVar.sectionRight G G (MonObj.one (X := G)) ≫
      (SemiCartesianMonoidalCategory.snd G G ≫ g) = g := by
    rw [← Category.assoc, Work.AbVar.sectionRight_snd, Category.id_comp]
  -- Precomposition with the section is a group homomorphism, so it commutes with `*` and `⁻¹`.
  simp only [Work.AbVar.homObstruction_eq]
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]
  rw [hμ, hf, hs]
  -- `g * (g 1)⁻¹ * g⁻¹ = 1` and `g 1 = 1` by hypothesis.
  rw [show SemiCartesianMonoidalCategory.toUnit G ≫ MonObj.one (X := H) = (1 : G ⟶ H) from rfl]
  simp

end Work.AbVar.Hom
