import Mathlib
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.PairSequence

/-!
# Naturality of the pair connecting homomorphism under a map of pairs

A continuous map `f : X₁ ⟶ X₂` with `f '' A₁ ⊆ A₂` induces a cochain map
`relComplexMap ℤ A₁ A₂ f h : C^*(X₂,A₂) ⟶ C^*(X₁,A₁)` (`Work.Cohomology.relComplexMap`), whose
absolute part is the pullback `dualChainMap f`.  This file records that the pair connecting
homomorphisms `pairδ` are natural with respect to these maps:

  `(f|A₁→A₂)^* ≫ δ_{(X₁,A₁)} = δ_{(X₂,A₂)} ≫ (relComplexMap)^*`.

This is the general form of the two naturalities used in the collar computation of the
derivation property of the Wang transgression (`D2_PLAN_SESSION_NEXT.md` §1 Step 5): the excision
comparison and the trivialisation comparison are both `relComplexMap`s of a map of pairs.
-/

open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

/-- The compatibility square of `relComplexMap` with the inclusion of the relative complex into
the absolute one (the explicit form of the `∃`-statement `Work.Cohomology.exists_relComplexMap`). -/
theorem relComplexMap_relIncl {X1 X2 : TopCat} (A1 : Set X1) (A2 : Set X2) (f : X1 ⟶ X2)
    (h : ∀ x ∈ A1, f x ∈ A2) :
    CategoryTheory.CategoryStruct.comp (Work.Cohomology.relComplexMap ℤ A1 A2 f h)
        (Work.Cohomology.relIncl ℤ X1 A1)
      = CategoryTheory.CategoryStruct.comp (Work.Cohomology.relIncl ℤ X2 A2)
          (Work.Cohomology.dualChainMap ℤ X1 X2 f) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Work.Cohomology.relComplexMap_f,
    Work.Cohomology.relIncl_f, Work.Cohomology.relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Work.Cohomology.relMapLM_coe ℤ A1 A2 f h n x

/-- **Naturality of the pair connecting homomorphism** under a map of pairs. -/
theorem pairDelta_relComplexMap {X1 X2 : TopCat} (A1 : Set X1) (A2 : Set X2) (f : X1 ⟶ X2)
    (h : ∀ x ∈ A1, f x ∈ A2) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp
        (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ (TopCat.of A1)
          (TopCat.of A2) (Work.Cohomology.relMapSub A1 A2 f h)) n)
        (Work.Cohomology.pairδ ℤ X1 A1 n)
      = CategoryTheory.CategoryStruct.comp
          (Work.Cohomology.pairδ ℤ X2 A2 n)
          (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap ℤ A1 A2 f h) (n + 1)) := by
  have hS2 : (Work.Cohomology.pairShort ℤ X1 A1).ShortExact :=
    Work.Cohomology.pairShort_shortExact ℤ X1 A1
  have hS1 : (Work.Cohomology.pairShort ℤ X2 A2).ShortExact :=
    Work.Cohomology.pairShort_shortExact ℤ X2 A2
  let φ : Work.Cohomology.pairShort ℤ X2 A2 ⟶ Work.Cohomology.pairShort ℤ X1 A1 :=
    ShortComplex.homMk (Work.Cohomology.relComplexMap ℤ A1 A2 f h)
      (Work.Cohomology.dualChainMap ℤ X1 X2 f)
      (Work.Cohomology.dualChainMap ℤ (TopCat.of A1) (TopCat.of A2)
        (Work.Cohomology.relMapSub A1 A2 f h))
      (relComplexMap_relIncl A1 A2 f h)
      (Work.Cohomology.dualChainMap_restr_comp ℤ A1 A2 f h)
  have hnat := HomologicalComplex.HomologySequence.δ_naturality φ hS1 hS2 n (n + 1)
    (by simp [ComplexShape.up])
  have h1 : hS1.δ n (n + 1) (by simp [ComplexShape.up]) = Work.Cohomology.pairδ ℤ X2 A2 n := rfl
  have h2 : hS2.δ n (n + 1) (by simp [ComplexShape.up]) = Work.Cohomology.pairδ ℤ X1 A1 n := rfl
  have ht1 : φ.τ₁ = Work.Cohomology.relComplexMap ℤ A1 A2 f h := rfl
  have ht3 : φ.τ₃ = Work.Cohomology.dualChainMap ℤ (TopCat.of A1) (TopCat.of A2)
      (Work.Cohomology.relMapSub A1 A2 f h) := rfl
  rw [← h1, ← h2, ← ht1, ← ht3]
  exact hnat.symm

end

end Work.StemsB
