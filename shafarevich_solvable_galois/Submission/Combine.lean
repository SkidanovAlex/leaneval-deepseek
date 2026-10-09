/-
Copyright (c) 2025. All rights reserved.

# Combining realizations

Two ways of combining Galois realizations are needed when building a field with a prescribed
solvable Galois group:

* moving a realization into a fixed algebraic closure, so that composita and intersections make
  sense (`RealizableOver.toClosure`);
* the Galois group of a compositum of two *linearly disjoint* Galois extensions is the product of
  the Galois groups (`Submission/Work/FieldTheory/gal_sup_prod`), whence a product of realizable
  groups whose realizations can be chosen linearly disjoint is realizable.
-/
import Mathlib
import Submission.Realization
import Submission.Work.FieldTheory.gal_sup_prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

universe u

open scoped Classical

/-- Realizations over `ℚ` can be taken inside `AlgebraicClosure ℚ`. -/
theorem RealizableOver.toClosure {G : Type*} [Group G] (h : RealizableOver ℚ G) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ L ∧ IsGalois ℚ L ∧
      Nonempty (G ≃* (L ≃ₐ[ℚ] L)) := by
  classical
  obtain ⟨K, hF, hA, hFD, hG, ⟨e⟩⟩ := h
  letI : Field K := hF
  letI : Algebra ℚ K := hA
  letI : FiniteDimensional ℚ K := hFD
  letI : IsGalois ℚ K := hG
  -- embed `K` into `AlgebraicClosure ℚ`
  let f : K →ₐ[ℚ] AlgebraicClosure ℚ :=
    IsAlgClosed.lift (R := ℚ) (S := K) (M := AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ ↥f.fieldRange :=
    (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional
  haveI : IsGalois ℚ ↥f.fieldRange := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField f)
  exact ⟨f.fieldRange, inferInstance, inferInstance,
    ⟨e.trans (AlgEquiv.autCongr (AlgEquiv.ofInjectiveField f))⟩⟩

/-- Conversely, a realization inside `AlgebraicClosure ℚ` is a realization. -/
theorem realizableOver_of_intermediateField {G : Type*} [Group G]
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (e : G ≃* (L ≃ₐ[ℚ] L)) : RealizableOver ℚ G :=
  ⟨↥L, inferInstance, inferInstance, inferInstance, inferInstance, ⟨e⟩⟩


/-! ## The Galois group of a compositum of two linearly disjoint Galois subextensions

`Work.FieldTheory.gal_sup_prod` computes `Gal(L ⊔ M / F) ≃* Gal(L/F) × Gal(M/F)` when
`L ⊓ M = ⊥`.  We record the immediate consequence for realizability: the product of the
two Galois groups is realizable over `F`. -/

/-- If `L` and `M` are finite Galois subextensions of `Ω/F` with `L ⊓ M = ⊥` (equivalently,
linearly disjoint), then the product `Gal(L/F) × Gal(M/F)` is realizable over `F` — namely by
the compositum `L ⊔ M`. -/
theorem realizableOver_prod_of_inf_eq_bot {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    (L M : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L]
    [FiniteDimensional F M] [IsGalois F M] (h : L ⊓ M = ⊥) :
    RealizableOver F ((L ≃ₐ[F] L) × (M ≃ₐ[F] M)) := by
  obtain ⟨e⟩ := @Work.FieldTheory.gal_sup_prod F Ω _ _ _ L M ‹FiniteDimensional F L› ‹IsGalois F L›
    ‹FiniteDimensional F M› ‹IsGalois F M› h
  haveI : FiniteDimensional F ↥(L ⊔ M) := inferInstance
  haveI : IsGalois F ↥(L ⊔ M) := ⟨⟩
  exact ⟨↥(L ⊔ M), inferInstance, inferInstance, inferInstance, inferInstance, ⟨e.symm⟩⟩

/-- The same statement for subfields of `AlgebraicClosure ℚ`, with all instances passed
explicitly (the `IntermediateField` coercions have several non-definitionally-equal `Algebra`
instance paths, so type class search cannot be relied upon here). -/
theorem realizableOver_prod_of_inf_eq_bot_closure
    (L M : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hLfd : FiniteDimensional ℚ L) (hLG : IsGalois ℚ L)
    (hMfd : FiniteDimensional ℚ M) (hMG : IsGalois ℚ M) (h : L ⊓ M = ⊥) :
    RealizableOver ℚ ((L ≃ₐ[ℚ] L) × (M ≃ₐ[ℚ] M)) :=
  @realizableOver_prod_of_inf_eq_bot ℚ (AlgebraicClosure ℚ) _ _ _ L M hLfd hLG hMfd hMG h

end Submission
