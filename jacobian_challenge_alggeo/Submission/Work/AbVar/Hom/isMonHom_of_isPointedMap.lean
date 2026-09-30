import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.Rigidity.rigid_isAlgClosed
import Submission.Work.AbVar.Hom.sectionLeft_homObstruction
import Submission.Work.AbVar.Hom.sectionRight_homObstruction
import Submission.Work.AbVar.Hom.isGroupHom_of_pointed_of_homObstruction_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.AbVar.Hom

open CategoryTheory AlgebraicGeometry

/-! ## The rigidity lemma over an arbitrary field

The rigidity lemma is proved first over an algebraically closed field
(`Work.AbVar.Rigidity.rigid_isAlgClosed`) and then descended to an arbitrary field `k` by base
changing along `Spec k̄ ⟶ Spec k`: the pullback functor `Over.pullback` along the (injective,
hence epi) field extension is faithful, and it is monoidal, which allows the two sides of the
rigidity identity to be compared after base change. -/

open CategoryTheory in
theorem rigidity_general {k : Type*} [Field k]
    {X Y Z : Work.AbVar.Sch k} [AlgebraicGeometry.IsProper X.hom]
    [AlgebraicGeometry.GeometricallyIntegral X.hom]
    [AlgebraicGeometry.GeometricallyIntegral Y.hom]
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
    [AlgebraicGeometry.IsSeparated Z.hom] [AlgebraicGeometry.LocallyOfFiniteType Z.hom]
    (y0 : Work.AbVar.Point Y) (f : MonoidalCategoryStruct.tensorObj X Y ⟶ Z)
    (c : Work.AbVar.Point Z)
    (hf : Work.AbVar.sectionLeft X Y y0 ≫ f = SemiCartesianMonoidalCategory.toUnit X ≫ c)
    (x0 : Work.AbVar.Point X) :
    f = SemiCartesianMonoidalCategory.snd X Y ≫ Work.AbVar.sectionRight X Y x0 ≫ f := by
  let κ := AlgebraicClosure k
  let φ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k κ))
  let F := Over.pullback φ
  let X' : Work.AbVar.Sch κ := F.obj X
  let Y' : Work.AbVar.Sch κ := F.obj Y
  let Z' : Work.AbVar.Sch κ := F.obj Z
  haveI : AlgebraicGeometry.IsProper X'.hom := by dsimp [X', F]; infer_instance
  haveI : AlgebraicGeometry.GeometricallyIntegral X'.hom := by dsimp [X', F]; infer_instance
  haveI : AlgebraicGeometry.GeometricallyIntegral Y'.hom := by dsimp [Y', F]; infer_instance
  haveI : AlgebraicGeometry.LocallyOfFiniteType Y'.hom := by dsimp [Y', F]; infer_instance
  haveI : AlgebraicGeometry.IsSeparated Z'.hom := by dsimp [Z', F]; infer_instance
  haveI : AlgebraicGeometry.LocallyOfFiniteType Z'.hom := by dsimp [Z', F]; infer_instance
  haveI : IsAlgClosed κ := inferInstance
  -- The graph section commutes with base change.
  have claim1 : F.map (Work.AbVar.sectionLeft X Y y0) =
      Work.AbVar.sectionLeft X' Y' (Functor.LaxMonoidal.ε F ≫ F.map y0) ≫
        Functor.LaxMonoidal.μ F X Y := by
    rw [Work.AbVar.sectionLeft, Work.AbVar.sectionLeft]
    rw [← Functor.Monoidal.lift_μ F (𝟙 X) (SemiCartesianMonoidalCategory.toUnit X ≫ y0)]
    congr 1
    congr 1
    · rw [CategoryTheory.Functor.map_id]
    · rw [Functor.map_comp, ← Functor.Monoidal.toUnit_ε F X]
      rfl
  -- The hypothesis descends.
  have hf' : Work.AbVar.sectionLeft X' Y' (Functor.LaxMonoidal.ε F ≫ F.map y0) ≫
        (Functor.LaxMonoidal.μ F X Y ≫ F.map f) =
      SemiCartesianMonoidalCategory.toUnit X' ≫ (Functor.LaxMonoidal.ε F ≫ F.map c) := by
    rw [← Category.assoc, ← claim1, ← Functor.map_comp, hf, Functor.map_comp,
      ← Functor.Monoidal.toUnit_ε F X, Category.assoc]
  have key := Work.AbVar.Rigidity.rigid_isAlgClosed (k := κ) (X := X') (Y := Y') (Z := Z')
      (Functor.LaxMonoidal.ε F ≫ F.map y0) (Functor.LaxMonoidal.μ F X Y ≫ F.map f)
      (Functor.LaxMonoidal.ε F ≫ F.map c) hf' (Functor.LaxMonoidal.ε F ≫ F.map x0)
  -- The bundle section commutes with base change.
  have hsec : F.map (Work.AbVar.sectionRight X Y x0) =
      Work.AbVar.sectionRight X' Y' (Functor.LaxMonoidal.ε F ≫ F.map x0) ≫
        Functor.LaxMonoidal.μ F X Y := by
    rw [Work.AbVar.sectionRight, Work.AbVar.sectionRight]
    rw [← Functor.Monoidal.lift_μ F (SemiCartesianMonoidalCategory.toUnit Y ≫ x0) (𝟙 Y)]
    congr 1
    congr 1
    · rw [Functor.map_comp, ← Functor.Monoidal.toUnit_ε F Y]
      rfl
    · rw [CategoryTheory.Functor.map_id]
  have hsnd : F.map (SemiCartesianMonoidalCategory.snd X Y) =
      (Functor.Monoidal.μIso F X Y).inv ≫ SemiCartesianMonoidalCategory.snd X' Y' := by
    rw [← Functor.Monoidal.μ_snd F X Y]
    exact (Iso.inv_hom_id_assoc (Functor.Monoidal.μIso F X Y)
      (F.map (SemiCartesianMonoidalCategory.snd X Y))).symm
  have hfinal : F.map f = F.map (SemiCartesianMonoidalCategory.snd X Y ≫
      Work.AbVar.sectionRight X Y x0 ≫ f) := by
    rw [Functor.map_comp, Functor.map_comp, hsnd, hsec]
    simp only [Category.assoc]
    rw [← key]
    exact (Iso.inv_hom_id_assoc (Functor.Monoidal.μIso F X Y) (F.map f)).symm
  exact F.map_injective hfinal

/- A pointed morphism between proper, geometrically integral group schemes over a field is a
homomorphism of group schemes.

The obstruction `homObstruction g = μ[G] ≫ g * (fst ≫ g)⁻¹ * (snd ≫ g)⁻¹ : G ⊗ G ⟶ H` vanishes
on the graph section `x ↦ (1, x)` (this is exactly pointedness). The rigidity lemma applied to
`homObstruction g` then forces it to be constant along the fibres of the second projection, and
its value on the graph section `x ↦ (1, x)` is the unit, so the obstruction is the unit of
`Hom(G ⊗ G, H)`; the general lemma `isGroupHom_of_pointed_of_homObstruction_eq_one` finishes. -/
open CategoryTheory in
theorem isMonHom_of_isPointedMap {k : Type*} [Field k] {G H : Work.AbVar.Sch k}
    [GrpObj G] [GrpObj H] [AlgebraicGeometry.IsProper G.hom]
    [AlgebraicGeometry.GeometricallyIntegral G.hom]
    [AlgebraicGeometry.IsProper H.hom] [AlgebraicGeometry.GeometricallyIntegral H.hom]
    (g : G ⟶ H)
    (hg : CategoryTheory.MonObj.one (X := G) ≫ g = CategoryTheory.MonObj.one (X := H)) :
    CategoryTheory.IsMonHom g := by
  -- The obstruction vanishes along the graph section `x ↦ (1, x)`.
  have hL := sectionLeft_homObstruction g hg
  -- Rigidity: `homObstruction g` is constant along the fibres of the second projection,
  -- so it is determined by its value on `x ↦ (1, x)`.
  have hR := rigidity_general (X := G) (Y := G) (Z := H)
    (MonObj.one (X := G)) (Work.AbVar.homObstruction g) (MonObj.one (X := H))
    hL (MonObj.one (X := G))
  -- Its value along the graph section `x ↦ (1, x)` is the unit.
  have hsecR := sectionRight_homObstruction g hg
  rw [hsecR] at hR
  -- Hence the obstruction is the unit of the group `Hom(G ⊗ G, H)`.
  refine isGroupHom_of_pointed_of_homObstruction_eq_one g hg ?_
  rw [hR, ← Category.assoc, SemiCartesianMonoidalCategory.comp_toUnit]

end Work.AbVar.Hom
