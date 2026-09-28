import Mathlib
import Submission.Work.Cohomology.pd_ab_enlarge

/-!
# Compatibility of `pdABInclRel` with the enlargement of the pair

Let `A' ⊆ A` and `B' ⊆ B` be subsets of a space `X`.  The enlargement map
`pdABEnlarge X hA hB : pdABCoh X A B ⟶ pdABCoh X A' B'` is the identity on the underlying
cochains, and likewise the map `pdRelComplexEnlargeUnion X hA hB` on the relative complexes of
the unions.  Consequently the square

```
relComplex ℤ X (A ∪ B) --pdABInclRel X A B--> pdABCoh X A B
        |                                          |
pdRelComplexEnlargeUnion                    pdABEnlarge
        v                                          v
relComplex ℤ X (A' ∪ B') --pdABInclRel X A' B'--> pdABCoh X A' B'
```

commutes.  This is the naturality of the inclusion `C^*(X, A∪B) ⟶ C^*(X, A+B)` with respect to
enlarging the compact set: both composites are the "same" inclusion of cochains
`relComplex ℤ X (A ∪ B) ⟶ pdABCoh X A' B'`.
-/

open CategoryTheory

namespace Work.Cohomology

noncomputable section

/-- The enlargement map of the `A+B` complex is the identity on the underlying cochains. -/
theorem pdABEnlarge_coe (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A) (hB : B' ⊆ B)
    (n : ℕ) (x : (pdABCoh X A B).X n) :
    ((ModuleCat.Hom.hom ((pdABEnlarge X hA hB).f n)) x).1 = x.1 := rfl

/-- The enlargement map on the relative complexes of the unions, `relComplexMap` induced by the
identity, is the identity on the underlying cochains. -/
theorem pdRelComplexEnlargeUnion_coe (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A)
    (hB : B' ⊆ B) (n : ℕ) (x : (relComplex ℤ X (A ∪ B)).X n) :
    ((ModuleCat.Hom.hom ((pdRelComplexEnlargeUnion X hA hB).f n)) x).1 = x.1 := by
  have key : (pdRelComplexEnlargeUnion X hA hB).f n
      = ModuleCat.ofHom
          (relMapLM ℤ (A' ∪ B') (A ∪ B) (𝟙 X) (Set.union_subset_union hA hB) n) :=
    relComplexMap_f ..
  have h1 : ModuleCat.Hom.hom ((pdRelComplexEnlargeUnion X hA hB).f n)
      = relMapLM ℤ (A' ∪ B') (A ∪ B) (𝟙 X) (Set.union_subset_union hA hB) n :=
    (congrArg ModuleCat.Hom.hom key).trans (ModuleCat.hom_ofHom _)
  rw [h1]
  exact (relMapLM_coe ℤ (A' ∪ B') (A ∪ B) (𝟙 X) (Set.union_subset_union hA hB) n x).trans
    (by rw [dualChainMap_id, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply])

/-- **The inclusion `C^*(X, A∪B) ⟶ C^*(X, A+B)` is natural under enlarging the pair.** -/
theorem pdABInclRel_comp_pdABEnlarge (X : TopCat) {A A' B B' : Set X} (hA : A' ⊆ A)
    (hB : B' ⊆ B) :
    CategoryTheory.CategoryStruct.comp (Work.Cohomology.pdABInclRel X A B)
        (Work.Cohomology.pdABEnlarge X hA hB)
      = CategoryTheory.CategoryStruct.comp (Work.Cohomology.pdRelComplexEnlargeUnion X hA hB)
        (Work.Cohomology.pdABInclRel X A' B') := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, pdABInclRel_coe, pdABEnlarge_coe]
  exact (pdRelComplexEnlargeUnion_coe X hA hB n x).symm

end

end Work.Cohomology
