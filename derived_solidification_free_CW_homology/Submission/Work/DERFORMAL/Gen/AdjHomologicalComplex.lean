/-
# Adjunctions between categories of homological complexes (prolongation)

If `F : C ⥤ D` and `G : D ⥤ C` are additive functors forming an adjunction `F ⊣ G`, then for any
complex shape `c` the induced ("prolongation") functors on homological complexes
`F.mapHomologicalComplex c` and `G.mapHomologicalComplex c` are again adjoint.  The unit and the
counit of the induced adjunction are the unit and the counit of `adj`, applied degreewise, and the
two triangle identities are checked componentwise (where they reduce to
`Adjunction.left_triangle_components` and `Adjunction.right_triangle_components`).

This is the `Nonempty` form requested by the DERFORMAL area (derived solidification, holes 4–7):
it transports an adjunction on the level of objects to an adjunction on the level of cochain
complexes.  The main work is the construction `mapHomologicalComplexAdjunction` below, whose
degreewise unit/counit are also exposed separately together with their component formulas.
-/
import Mathlib

namespace Work.DERFORMAL.Gen

open CategoryTheory

variable {ι : Type*} {C : Type*} {D : Type*} [Category C] [Preadditive C] [Category D]
  [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]

/-- The unit of the adjunction between categories of homological complexes induced by an additive
adjunction `F ⊣ G`: the unit of `adj`, applied degreewise.  Naturality is the naturality of the
unit of `adj` on the components. -/
def mapHomologicalComplexUnit (adj : F ⊣ G) (c : ComplexShape ι) :
    𝟭 (HomologicalComplex C c) ⟶ F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c where
  app K := HomologicalComplex.Hom.mk (fun i => adj.unit.app (K.X i)) (fun _ _ _ => by simp)
  naturality := fun {K L} f => by ext i; simp

/-- The counit of the adjunction between categories of homological complexes induced by an additive
adjunction `F ⊣ G`: the counit of `adj`, applied degreewise. -/
def mapHomologicalComplexCounit (adj : F ⊣ G) (c : ComplexShape ι) :
    G.mapHomologicalComplex c ⋙ F.mapHomologicalComplex c ⟶ 𝟭 (HomologicalComplex D c) where
  app L := HomologicalComplex.Hom.mk (fun i => adj.counit.app (L.X i)) (fun _ _ _ => by simp)
  naturality := fun {K L} f => by ext i; simp

@[simp]
lemma mapHomologicalComplexUnit_app_f (adj : F ⊣ G) (c : ComplexShape ι)
    (K : HomologicalComplex C c) (i : ι) :
    ((mapHomologicalComplexUnit adj c).app K).f i = adj.unit.app (K.X i) := rfl

@[simp]
lemma mapHomologicalComplexCounit_app_f (adj : F ⊣ G) (c : ComplexShape ι)
    (K : HomologicalComplex D c) (i : ι) :
    ((mapHomologicalComplexCounit adj c).app K).f i = adj.counit.app (K.X i) := rfl

/-- An additive adjunction `F ⊣ G` induces an adjunction between the associated ("prolongation")
functors on homological complexes, for any complex shape `c`. -/
def mapHomologicalComplexAdjunction (adj : F ⊣ G) (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c :=
  Adjunction.mk (mapHomologicalComplexUnit adj c) (mapHomologicalComplexCounit adj c)
    (fun X => by ext i; simp)
    (fun Y => by ext i; simp)

theorem AdjHomologicalComplex {ι : Type*} {C : Type*} {D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G) (c : ComplexShape ι) : Nonempty (F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c) := by
  exact ⟨mapHomologicalComplexAdjunction adj c⟩

end Work.DERFORMAL.Gen
