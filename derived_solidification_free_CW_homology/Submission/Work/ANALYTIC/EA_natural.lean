import Mathlib
import Submission.Work.ATOM.Toolkit.EA
import Submission.Work.ATOM.zfreeTensorIso_natural
import Submission.Work.ATOM.Defs

/-!
# Naturality of the epimorphism `EA`

`Work.ATOM.EA S : ℤ[(ℕ∪{∞}) × S] ⟶ P ⊗ ℤ[S]` is the quotient projection killing
`{∞} × S` (area `ATOM`).  Here we prove that the family `S ↦ EA S` is natural in the
light profinite set `S`, which is what makes the explicit `ATOM` maps available in
the `ANALYTIC` Čech/homotopy argument (holes 10 of the blueprint).

The proof is the naturality of the monoidal constraint `μ : ℤ[X] ⊗ ℤ[Y] ≅ ℤ[X × Y]`
(`Work.ATOM.zfreeTensorIso`) combined with the interchange law for whiskerings;
`Work.ATOM.zfreeTensorIso_natural` (already in the workspace) supplies the
naturality of `μ` in the second variable.
-/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid

private lemma zmap_id_eq (X : LightProfinite.{0}) :
    Work.ATOM.zmap (𝟙 X) = 𝟙 (Work.ATOM.zfree X) := by
  simp only [Work.ATOM.zmap, Functor.comp_map]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

private lemma zmap_id_whiskerRight_eq (X Y : LightProfinite.{0}) :
    Work.ATOM.zmap (𝟙 X ▷ Y) = 𝟙 (Work.ATOM.zfree (X ⊗ Y)) := by
  rw [CategoryTheory.MonoidalCategory.id_whiskerRight, zmap_id_eq]

theorem EA_natural {S T : LightProfinite.{0}} (f : T ⟶ S) :
    Work.ATOM.EA T ≫ (P ◁ Work.ATOM.zmap f) =
      Work.ATOM.zmap ((ℕ∪{∞}) ◁ f) ≫ Work.ATOM.EA S := by
  -- Naturality of `μ : ℤ[X] ⊗ ℤ[Y] ≅ ℤ[X × Y]` in the second variable, at `X = ℕ∪{∞}`.
  have nat := Work.ATOM.zfreeTensorIso_natural (X := (ℕ∪{∞})) (X' := (ℕ∪{∞}))
      (Y := T) (Y' := S) (𝟙 (ℕ∪{∞})) f
  rw [zmap_id_whiskerRight_eq, zmap_id_eq, CategoryTheory.MonoidalCategory.id_whiskerRight]
    at nat
  simp only [Category.id_comp, Category.comp_id] at nat
  -- Consequently the *inverse* of `μ` is natural as well.
  have hinv : (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) T).inv ≫
      ((Work.ATOM.zfree (ℕ∪{∞})) ◁ Work.ATOM.zmap f)
      = Work.ATOM.zmap ((ℕ∪{∞}) ◁ f) ≫ (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, nat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- Expand `EA` and assemble with the interchange law `whisker_exchange`.
  simp only [Work.ATOM.EA]
  calc ((Work.ATOM.zfreeTensorIso (ℕ∪{∞}) T).inv ≫ P_proj ▷ Work.ATOM.zfree T) ≫
        (P ◁ Work.ATOM.zmap f)
      = (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) T).inv ≫
          ((P_proj ▷ Work.ATOM.zfree T) ≫ (P ◁ Work.ATOM.zmap f)) :=
        Category.assoc _ _ _
    _ = (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) T).inv ≫
          (((Work.ATOM.zfree (ℕ∪{∞})) ◁ Work.ATOM.zmap f) ≫ (P_proj ▷ Work.ATOM.zfree S)) := by
        rw [← CategoryTheory.MonoidalCategory.whisker_exchange P_proj (Work.ATOM.zmap f)]
    _ = ((Work.ATOM.zfreeTensorIso (ℕ∪{∞}) T).inv ≫
            ((Work.ATOM.zfree (ℕ∪{∞})) ◁ Work.ATOM.zmap f))
          ≫ (P_proj ▷ Work.ATOM.zfree S) := (Category.assoc _ _ _).symm
    _ = (Work.ATOM.zmap ((ℕ∪{∞}) ◁ f) ≫ (Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv)
          ≫ (P_proj ▷ Work.ATOM.zfree S) := by rw [hinv]
    _ = Work.ATOM.zmap ((ℕ∪{∞}) ◁ f) ≫
          ((Work.ATOM.zfreeTensorIso (ℕ∪{∞}) S).inv ≫ (P_proj ▷ Work.ATOM.zfree S)) :=
        Category.assoc _ _ _

end Work.ANALYTIC
