import Mathlib
import Submission.Work.AbVar.P1Action.Points

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace Work.AbVar

/-- **Naturality of `sectionLeft` in the first variable.**
For a morphism `f : X ⟶ X'` and a point `y : 𝟙_ C ⟶ Y`,
the graph section at `y` is natural in the first component:
`f ≫ sectionLeft X' Y y = sectionLeft X Y y ≫ (f ⊗ₘ 𝟙 Y)`.

This is a purely monoidal-categorical fact about the cartesian monoidal structure; here it is
used for `C = Sch k`, `f = gmToP1 k`, `X = 𝔾_m`, `X' = ℙ¹`, `Y = 𝔾_m`. -/
lemma sectionLeft_naturality {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X X' Y : C} (f : X ⟶ X') (y : 𝟙_ C ⟶ Y) :
    f ≫ lift (𝟙 X') (toUnit X' ≫ y) = lift (𝟙 X) (toUnit X ≫ y) ≫ (f ⊗ₘ 𝟙 Y) := by
  rw [comp_lift, lift_map]
  congr 1
  · rw [Category.comp_id, Category.id_comp]
  · rw [Category.comp_id, ← Category.assoc, toUnit_unique (f ≫ toUnit X') (toUnit X)]

end Work.AbVar

namespace Work.AbVar.P1Action

open Work.AbVar

/-- The graph section of `ℙ¹ ⊗ 𝔾_m` (at the unit point of `𝔾_m`), composed with the open
immersion `𝔾_m ⟶ ℙ¹` `T ↦ [T : 1]`, agrees with the graph section of `𝔾_m ⊗ 𝔾_m` followed by
`gmToP1 ⊗ 𝟙`. This is naturality of `sectionLeft` in the first variable applied to `gmToP1`. -/
theorem gmToP1_sectionLeft (k : Type*) [Field k] :
    CategoryTheory.CategoryStruct.comp (Work.AbVar.P1Action.gmToP1 k)
        (Work.AbVar.sectionLeft (Work.AbVar.P1 k) (Work.AbVar.Gm k)
          (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k)))
      = CategoryTheory.CategoryStruct.comp
          (Work.AbVar.sectionLeft (Work.AbVar.Gm k) (Work.AbVar.Gm k)
            (CategoryTheory.MonObj.one (X := Work.AbVar.Gm k)))
          (CategoryTheory.MonoidalCategoryStruct.tensorHom (Work.AbVar.P1Action.gmToP1 k)
            (CategoryTheory.CategoryStruct.id (Work.AbVar.Gm k))) := by
  simpa only [Work.AbVar.sectionLeft] using
    Work.AbVar.sectionLeft_naturality (C := Sch k) (X := Gm k) (X' := P1 k) (Y := Gm k)
      (P1Action.gmToP1 k) (MonObj.one (X := Gm k))

end Work.AbVar.P1Action
