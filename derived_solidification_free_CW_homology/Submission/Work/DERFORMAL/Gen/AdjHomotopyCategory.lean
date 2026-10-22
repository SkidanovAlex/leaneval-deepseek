import Mathlib

namespace Work.DERFORMAL.Gen

open CategoryTheory

/-- Auxiliary: an additive adjunction of preadditive categories induces an adjunction between the
categories of homological complexes. -/
noncomputable def adjMapHomologicalComplexUnit {ι : Type*} {C : Type*} {D : Type*} [Category C]
    [Preadditive C] [Category D] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    (adj : F ⊣ G) (c : ComplexShape ι) :
    𝟭 (HomologicalComplex C c) ⟶ F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c where
  app K := HomologicalComplex.Hom.mk (fun i => adj.unit.app (K.X i))
    (fun i j _ => (adj.unit.naturality (K.d i j)).symm)
  naturality := by
    intro K L f
    ext i
    simp only [HomologicalComplex.comp_f]
    exact adj.unit.naturality (f.f i)

/-- Auxiliary: the counit of the adjunction on homological complexes. -/
noncomputable def adjMapHomologicalComplexCounit {ι : Type*} {C : Type*} {D : Type*} [Category C]
    [Preadditive C] [Category D] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    (adj : F ⊣ G) (c : ComplexShape ι) :
    G.mapHomologicalComplex c ⋙ F.mapHomologicalComplex c ⟶ 𝟭 (HomologicalComplex D c) where
  app L := HomologicalComplex.Hom.mk (fun i => adj.counit.app (L.X i))
    (fun i j _ => (adj.counit.naturality (L.d i j)).symm)
  naturality := by
    intro L M g
    ext i
    simp only [HomologicalComplex.comp_f]
    exact adj.counit.naturality (g.f i)

/-- Auxiliary: an additive adjunction induces an adjunction of the prolongations to homological
complexes. -/
noncomputable def adjMapHomologicalComplex {ι : Type*} {C : Type*} {D : Type*} [Category C]
    [Preadditive C] [Category D] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    (adj : F ⊣ G) (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c :=
  Adjunction.mk (adjMapHomologicalComplexUnit adj c) (adjMapHomologicalComplexCounit adj c)
    (by
      intro K
      ext i
      dsimp only [adjMapHomologicalComplexUnit, adjMapHomologicalComplexCounit]
      exact adj.left_triangle_components (K.X i))
    (by
      intro L
      ext i
      dsimp only [adjMapHomologicalComplexUnit, adjMapHomologicalComplexCounit]
      exact adj.right_triangle_components (L.X i))

/-- An additive adjunction `F ⊣ G` between preadditive categories induces an adjunction between the
corresponding homotopy categories of homological complexes of shape `c`, for any `ComplexShape c`.

The unit and counit are obtained by descending the unit and counit of the adjunction on
homological complexes through the quotient functors defining the homotopy categories. -/
theorem AdjHomotopyCategory {ι : Type*} {C : Type*} {D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G) (c : ComplexShape ι) : Nonempty (F.mapHomotopyCategory c ⊣ G.mapHomotopyCategory c) := by
  classical
  have adjh : F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c := adjMapHomologicalComplex adj c
  -- The unit of the induced adjunction, defined on representatives.
  let τ : HomotopyCategory.quotient C c ⟶
      HomotopyCategory.quotient C c ⋙ F.mapHomotopyCategory c ⋙ G.mapHomotopyCategory c :=
    { app := fun K => (HomotopyCategory.quotient C c).map (adjh.unit.app K)
      naturality := by
        intro K L g
        change (HomotopyCategory.quotient C c).map g ≫
            (HomotopyCategory.quotient C c).map (adjh.unit.app L) =
          (HomotopyCategory.quotient C c).map (adjh.unit.app K) ≫
            (G.mapHomotopyCategory c).map
              ((F.mapHomotopyCategory c).map ((HomotopyCategory.quotient C c).map g))
        rw [CategoryTheory.Functor.mapHomotopyCategory_map,
          CategoryTheory.Functor.mapHomotopyCategory_map,
          ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        exact congrArg (fun x => (HomotopyCategory.quotient C c).map x) (adjh.unit.naturality g) }
  let u : 𝟭 (HomotopyCategory C c) ⟶ F.mapHomotopyCategory c ⋙ G.mapHomotopyCategory c :=
    CategoryTheory.Quotient.natTransLift (homotopic C c) τ
  have hu : ∀ (K : HomologicalComplex C c), u.app ((HomotopyCategory.quotient C c).obj K) =
      (HomotopyCategory.quotient C c).map (adjh.unit.app K) := fun K =>
    CategoryTheory.Quotient.natTransLift_app (homotopic C c) _ _ _ K
  -- The counit of the induced adjunction, defined on representatives.
  let σ : HomotopyCategory.quotient D c ⋙ G.mapHomotopyCategory c ⋙ F.mapHomotopyCategory c ⟶
      HomotopyCategory.quotient D c :=
    { app := fun L => (HomotopyCategory.quotient D c).map (adjh.counit.app L)
      naturality := by
        intro L M g
        change (F.mapHomotopyCategory c).map
              ((G.mapHomotopyCategory c).map ((HomotopyCategory.quotient D c).map g)) ≫
            (HomotopyCategory.quotient D c).map (adjh.counit.app M) =
          (HomotopyCategory.quotient D c).map (adjh.counit.app L) ≫
            (HomotopyCategory.quotient D c).map g
        rw [CategoryTheory.Functor.mapHomotopyCategory_map,
          CategoryTheory.Functor.mapHomotopyCategory_map,
          ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        exact congrArg (fun x => (HomotopyCategory.quotient D c).map x)
          (adjh.counit.naturality g) }
  let v : G.mapHomotopyCategory c ⋙ F.mapHomotopyCategory c ⟶ 𝟭 (HomotopyCategory D c) :=
    CategoryTheory.Quotient.natTransLift (homotopic D c) σ
  have hv : ∀ (L : HomologicalComplex D c), v.app ((HomotopyCategory.quotient D c).obj L) =
      (HomotopyCategory.quotient D c).map (adjh.counit.app L) := fun L =>
    CategoryTheory.Quotient.natTransLift_app (homotopic D c) _ _ _ L
  refine ⟨Adjunction.mk u v ?_ ?_⟩
  · -- left triangle identity
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    rw [hu K, CategoryTheory.Functor.mapHomotopyCategory_map]
    change (HomotopyCategory.quotient D c).map
        ((F.mapHomologicalComplex c).map (adjh.unit.app K)) ≫
      v.app ((HomotopyCategory.quotient D c).obj ((F.mapHomologicalComplex c).obj K)) =
      𝟙 ((HomotopyCategory.quotient D c).obj ((F.mapHomologicalComplex c).obj K))
    rw [hv ((F.mapHomologicalComplex c).obj K), ← CategoryTheory.Functor.map_comp,
      adjh.left_triangle_components K]
    simp
  · -- right triangle identity
    intro Y
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    rw [hv L, CategoryTheory.Functor.mapHomotopyCategory_map]
    change u.app ((HomotopyCategory.quotient C c).obj ((G.mapHomologicalComplex c).obj L)) ≫
      (HomotopyCategory.quotient C c).map ((G.mapHomologicalComplex c).map (adjh.counit.app L)) =
      𝟙 ((HomotopyCategory.quotient C c).obj ((G.mapHomologicalComplex c).obj L))
    rw [hu ((G.mapHomologicalComplex c).obj L), ← CategoryTheory.Functor.map_comp,
      adjh.right_triangle_components L]
    simp

end Work.DERFORMAL.Gen
