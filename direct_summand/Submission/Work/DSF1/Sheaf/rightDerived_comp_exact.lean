import Mathlib

/-!
# Right derived functors commute with a functor preserving homology

If `F : C ⥤ D` is additive, `G : D ⥤ E` is additive and preserves homology (i.e. is
exact), then the `q`-th right derived functor of the composite `F ⋙ G` is obtained by
applying `G` to the `q`-th right derived functor of `F`:

  `((F ⋙ G).rightDerived q).obj A ≅ G.obj ((F.rightDerived q).obj A)`.

The right derived functors are defined through a chosen injective resolution `I` of `A`:
`(F.rightDerived q).obj A` is the `q`-th homology of the complex `F(I.cocomplex)`. Since
`G` preserves homology, it commutes with the homology of a complex
(`homologyFunctor_mapHomologicalComplex_iso` below), and since `G` applied to a
homological complex commutes definitionally with the complex of `G ∘ F`
(`(F ⋙ G).mapHomologicalComplex c = F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c`
at the level of objects), the result follows by composing the two `isoRightDerivedObj`
isomorphisms with this homology comparison isomorphism.
-/

universe u v w x p q

namespace Work.DSF1.Sheaf

open CategoryTheory CategoryTheory.Limits

/-- A functor `G` which preserves homology commutes with the homology functor on
homological complexes: the `i`-th homology of `G` applied to a complex `K` is
`G` applied to the `i`-th homology of `K`.

This is immediate from the description of the homology of a complex as the homology of
the short complex `K.sc i` and the corresponding statement for short complexes. -/
noncomputable def homologyFunctor_mapHomologicalComplex_iso {C : Type u} [Category.{v} C]
    [Abelian C] {D : Type w} [Category.{x} D] [Abelian D]
    (G : C ⥤ D) [G.Additive] [G.PreservesHomology]
    {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex C c) (i : ι) :
    ((HomologicalComplex.homologyFunctor D c i).obj ((G.mapHomologicalComplex c).obj K) ≅
      G.obj ((HomologicalComplex.homologyFunctor C c i).obj K)) :=
  ShortComplex.mapHomologyIso (K.sc i) G

theorem rightDerived_comp_exact {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.EnoughInjectives C]
    {D : Type w} [CategoryTheory.Category.{x} D] [CategoryTheory.Abelian D]
    [CategoryTheory.EnoughInjectives D]
    {E : Type p} [CategoryTheory.Category.{q} E] [CategoryTheory.Abelian E]
    (F : CategoryTheory.Functor C D) [F.Additive]
    (G : CategoryTheory.Functor D E) [G.Additive] [G.PreservesHomology]
    (A : C) (q : ℕ) :
    Nonempty (((CategoryTheory.Functor.comp F G).rightDerived q).obj A ≅
      G.obj ((F.rightDerived q).obj A)) := by
  classical
  refine ⟨?_⟩
  -- Fix a chosen injective resolution of `A`.
  let c : ComplexShape ℕ := ComplexShape.up ℕ
  let I : InjectiveResolution A := injectiveResolution A
  let M : CochainComplex C ℕ := I.cocomplex
  -- `(F ⋙ G).rightDerived q` computed on the resolution `I`.
  have iso1 := I.isoRightDerivedObj (F ⋙ G) q
  -- `G` commutes with homology, applied to the complex `F(I.cocomplex)`.
  have iso3 := homologyFunctor_mapHomologicalComplex_iso G c ((F.mapHomologicalComplex c).obj M) q
  -- `F.rightDerived q` computed on the resolution `I`, pushed forward by `G`.
  have iso4 := G.mapIso (I.isoRightDerivedObj F q)
  exact iso1 ≪≫ iso3 ≪≫ iso4.symm

end Work.DSF1.Sheaf
