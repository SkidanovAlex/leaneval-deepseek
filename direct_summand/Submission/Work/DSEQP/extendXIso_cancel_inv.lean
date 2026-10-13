import Mathlib
import Submission.Work.DSEQP.PerfChainAux

/-!
# Cancellation of the degree-`0` `extendXIso` comparisons

Let `F : C ⥤ D` be an additive functor between preadditive categories with zero objects,
`K : CochainComplex C ℕ`, and `e = ComplexShape.embeddingUpNat : ℕ ↪ ℤ`.

`Work.DSEQP.mapHomologicalComplexExtendUpNatIso F K` is the comparison isomorphism

`(F.mapHomologicalComplex (up ℤ)).obj (K.extend e) ≅ ((F.mapHomologicalComplex (up ℕ)).obj K).extend e`

whose component at an index `i'` is `Work.DSEQP.extendXCompIso F K (e.r i')`, which is the
identity on the indices in the image of `e` (and an arbitrary isomorphism of the two zero
objects on the other indices).

The main result, `Work.DSEQP.extendXIso_cancel_inv`, is the degree-`0` statement that this
comparison, conjugated by the canonical isomorphisms `K.extendXIso e h` (on the source) and
`F` applied to them (on the target), is the identity.

The proof is done by heterogeneous equality: on a `HEq` goal the index rewriting
`e.r (e.f i) ↝ some i` is allowed (`ComplexShape.Embedding.r_eq_some`), whereas it is not
possible in the ambient (ill-typed) goal.  The three factors are each shown to be `HEq` to an
identity, and `CategoryTheory.heq_comp` combines them.

## Main results

* `Work.DSEQP.extendXIso_hom_eqToHom`, `Work.DSEQP.extendXIso_inv_eqToHom`: componentwise
  computation of `K.extendXIso e h`.
* `Work.DSEQP.extendXCompIso_inv_heq`, `Work.DSEQP.extendXIso_inv_heq`,
  `Work.DSEQP.map_extendXIso_hom_heq`: the `HEq`-to-identity statements.
* `Work.DSEQP.extendXIso_cancel_inv_gen`: the cancellation in all degrees.
* `Work.DSEQP.extendXIso_cancel_inv`: the degree-`0` statement.
-/

open CategoryTheory Category Limits

namespace Work.DSEQP

section ExtendXIso

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]

/-- The `hom` of `K.extendXIso e h`, as an `eqToHom`. -/
theorem extendXIso_hom_eqToHom (K : CochainComplex C ℕ) (i : ℕ) (i' : ℤ)
    (h : ComplexShape.embeddingUpNat.f i = i') :
    (K.extendXIso ComplexShape.embeddingUpNat h).hom =
      eqToHom (congrArg (HomologicalComplex.extend.X K)
        (ComplexShape.Embedding.r_eq_some (e := ComplexShape.embeddingUpNat) h)) := by
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
    CategoryTheory.eqToIso.hom]

/-- The `inv` of `K.extendXIso e h`, as an `eqToHom`. -/
theorem extendXIso_inv_eqToHom (K : CochainComplex C ℕ) (i : ℕ) (i' : ℤ)
    (h : ComplexShape.embeddingUpNat.f i = i') :
    (K.extendXIso ComplexShape.embeddingUpNat h).inv =
      eqToHom (congrArg (HomologicalComplex.extend.X K)
        (ComplexShape.Embedding.r_eq_some (e := ComplexShape.embeddingUpNat) h)).symm := by
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
    CategoryTheory.eqToIso.inv]

variable (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)

/-- The component at `e.r i'` of the comparison isomorphism is (heterogeneously) the identity. -/
theorem extendXCompIso_inv_heq (i : ℕ) (i' : ℤ)
    (h : ComplexShape.embeddingUpNat.f i = i') :
    HEq (extendXCompIso F K (ComplexShape.embeddingUpNat.r i')).inv
      (𝟙 (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X i)) := by
  rw [ComplexShape.Embedding.r_eq_some (e := ComplexShape.embeddingUpNat) h]
  exact heq_of_eq rfl

/-- The inverse of `extendXIso` is (heterogeneously) the identity. -/
theorem extendXIso_inv_heq (i : ℕ) (i' : ℤ)
    (h : ComplexShape.embeddingUpNat.f i = i') :
    HEq ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
        ComplexShape.embeddingUpNat h).inv)
      (𝟙 (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X i)) := by
  rw [extendXIso_inv_eqToHom]
  exact eqToHom_heq_id_dom _ _ _

/-- The image under `F` of `K.extendXIso e h` is (heterogeneously) the identity. -/
theorem map_extendXIso_hom_heq (i : ℕ) (i' : ℤ)
    (h : ComplexShape.embeddingUpNat.f i = i') :
    HEq (F.map ((K.extendXIso ComplexShape.embeddingUpNat h).hom))
      (𝟙 (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X i)) := by
  rw [extendXIso_hom_eqToHom]
  rw [map_eqToHom_of]
  exact eqToHom_heq_id_cod _ _ _

/-- The degree-`i` cancellation: the comparison isomorphism, conjugated by
`extendXIso` on both sides, is the identity. -/
theorem extendXIso_cancel_inv_gen (i : ℕ) (i' : ℤ)
    (h : ComplexShape.embeddingUpNat.f i = i') :
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.CategoryStruct.comp
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
            ComplexShape.embeddingUpNat h).inv)
        ((mapHomologicalComplexExtendUpNatIso F K).inv.f i'))
      (F.map ((K.extendXIso ComplexShape.embeddingUpNat h).hom)) =
    𝟙 (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X i) := by
  rw [mapHomologicalComplexExtendUpNatIso_inv_f]
  let X₀ : D := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X i
  let p : HomologicalComplex.extend.X ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        (ComplexShape.embeddingUpNat.r i') =
      HomologicalComplex.extend.X ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        (some i) :=
    congrArg (HomologicalComplex.extend.X ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))
      (ComplexShape.Embedding.r_eq_some (e := ComplexShape.embeddingUpNat) h)
  let q : F.obj (HomologicalComplex.extend.X K (ComplexShape.embeddingUpNat.r i')) =
      F.obj (HomologicalComplex.extend.X K (some i)) :=
    congrArg (fun o => F.obj (HomologicalComplex.extend.X K o))
      (ComplexShape.Embedding.r_eq_some (e := ComplexShape.embeddingUpNat) h)
  have h1 : HEq (CategoryTheory.CategoryStruct.comp
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
            ComplexShape.embeddingUpNat h).inv)
        ((extendXCompIso F K (ComplexShape.embeddingUpNat.r i')).inv))
      (CategoryTheory.CategoryStruct.comp (𝟙 X₀) (𝟙 X₀)) :=
    heq_comp rfl p q (extendXIso_inv_heq F K i i' h)
      (extendXCompIso_inv_heq F K i i' h)
  have h2 : HEq (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp
          ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
              ComplexShape.embeddingUpNat h).inv)
          ((extendXCompIso F K (ComplexShape.embeddingUpNat.r i')).inv))
        (F.map ((K.extendXIso ComplexShape.embeddingUpNat h).hom)))
      (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.CategoryStruct.comp (𝟙 X₀) (𝟙 X₀)) (𝟙 X₀)) :=
    heq_comp rfl q rfl h1 (map_extendXIso_hom_heq F K i i' h)
  refine eq_of_heq (h2.trans (heq_of_eq ?_))
  rw [Category.comp_id, Category.comp_id]

end ExtendXIso

theorem extendXIso_cancel_inv {C D : Type*} [CategoryTheory.Category C] [CategoryTheory.Category D]
    [CategoryTheory.Preadditive C] [CategoryTheory.Preadditive D]
    [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.Limits.HasZeroObject D]
    (F : CategoryTheory.Functor C D) [F.Additive] (K : CochainComplex C ℕ) :
    CategoryTheory.CategoryStruct.comp
      (CategoryTheory.CategoryStruct.comp
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendXIso
            ComplexShape.embeddingUpNat (i := 0) rfl).inv)
        ((Work.DSEQP.mapHomologicalComplexExtendUpNatIso F K).inv.f 0))
      (F.map ((K.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom)) =
    CategoryTheory.CategoryStruct.id (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X 0) := by
  exact extendXIso_cancel_inv_gen F K 0 0 rfl

end Work.DSEQP
