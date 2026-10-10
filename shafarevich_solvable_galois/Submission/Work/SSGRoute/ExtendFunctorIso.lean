import Mathlib.Tactic.Have
import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# An additive functor commutes with `HomologicalComplex.extend`

For an additive functor `F : C ⥤ D` and a chain complex `K : ChainComplex C ℕ`, we construct the
canonical isomorphism
`((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).extend ComplexShape.embeddingDownNat ≅
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend ComplexShape.embeddingDownNat)`.

This is the shape-translation used to move the chain-level datum `φ` of
`Work.SSGRoute.mapExtAddHom_extMk` from `ChainComplex`-`ℕ`-language into
`CochainComplex`-`ℤ`-language, where the `Ext`/`Cocycle` API lives.
-/

open CategoryTheory Limits

namespace Work.SSGRoute

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category D] [Abelian D]
variable (F : C ⥤ D) [F.Additive]

/-- The components of the canonical isomorphism, indexed by `Option ℕ`. -/
noncomputable def extendFunctorIsoComp (K : ChainComplex C ℕ) (o : Option ℕ) :
    HomologicalComplex.extend.X ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) o ≅
    F.obj (HomologicalComplex.extend.X K o) :=
  match o with
  | none => (HomologicalComplex.extend.isZero_X ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K)
        (rfl : (none : Option ℕ) = none)).iso
      (Functor.map_isZero F (HomologicalComplex.extend.isZero_X K (rfl : (none : Option ℕ) = none)))
  | some k => by
      change HomologicalComplex.extend.X ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) (some k) ≅
        F.obj (HomologicalComplex.extend.X K (some k))
      exact Iso.refl _

/-- The extension of a chain complex along `ComplexShape.embeddingDownNat` commutes with an
additive functor. -/
noncomputable def extendFunctorIso (K : ChainComplex C ℕ) :
    (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).extend ComplexShape.embeddingDownNat) ≅
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend ComplexShape.embeddingDownNat)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i' => extendFunctorIsoComp F K (ComplexShape.embeddingDownNat.r i')) (by
    intro i j hij
    dsimp only [HomologicalComplex.extend, CategoryTheory.Functor.mapHomologicalComplex_obj_d]
    have key2 : ∀ (o₁ o₂ : Option ℕ),
        (extendFunctorIsoComp F K o₁).hom ≫ F.map (HomologicalComplex.extend.d K o₁ o₂) =
          HomologicalComplex.extend.d ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) o₁ o₂ ≫
            (extendFunctorIsoComp F K o₂).hom := by
      intro o₁ o₂
      cases o₁ <;> cases o₂ <;>
        dsimp only [extendFunctorIsoComp, HomologicalComplex.extend.d]
      all_goals try rw [Iso.refl_hom]
      all_goals try rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d]
      all_goals try rw [Functor.map_zero]
      all_goals try erw [Limits.comp_zero]
      all_goals try erw [Limits.zero_comp]
      all_goals try erw [Category.id_comp]
      all_goals try erw [Category.comp_id]
      all_goals try rfl
    exact key2 _ _)


/-- The components of `extendFunctorIso` intertwine the `extend`-comparison isomorphisms. -/
lemma extendFunctorIso_hom_extendXIso (K : ChainComplex C ℕ) (k : ℕ) (o : Option ℕ)
    (ho : o = some k) :
    (extendFunctorIsoComp F K o).hom ≫
        F.map ((HomologicalComplex.extend.XIso K ho).hom) =
      (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) ho).hom := by
  cases o with
  | none => exact absurd ho (by simp)
  | some k' =>
    have hk : k' = k := Option.some.inj ho
    subst hk
    rw [show ho = (rfl : (some k' : Option ℕ) = some k') from Subsingleton.elim _ _]
    rw [show extendFunctorIsoComp F K (some k') = Iso.refl _ from rfl]
    simp only [HomologicalComplex.extend.XIso, CategoryTheory.eqToIso, Iso.refl_hom,
      CategoryTheory.eqToHom_map]
    erw [Category.id_comp]
    congr 1

end Work.SSGRoute
