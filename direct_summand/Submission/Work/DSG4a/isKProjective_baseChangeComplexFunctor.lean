import Mathlib
import Submission.Work.DSG4a.BaseChangeComplex

/-!
# DSG4a: K-projectivity is preserved by base change

A bounded-above cochain complex `K` of projective `A`-modules is K-projective
(`CochainComplex.isKProjective_of_projective`).  Base change to an `A`-algebra `A'` preserves both
ingredients:

* the terms `A' ⊗[A] K.X n` are projective `A'`-modules, because `extendScalars (algebraMap A A')`
  is left adjoint to `restrictScalars (algebraMap A A')`, and restriction of scalars preserves
  epimorphisms (`Adjunction.map_projective`);
* the base-changed complex is still strictly bounded above by `d`, since `extendScalars` preserves
  zero objects (`Functor.map_isZero`, using that a left adjoint preserves zero morphisms).

Hence `baseChangeComplexFunctor.obj K` is K-projective over `A'`.
-/

open CategoryTheory Limits

universe u

namespace Work.DSG4a

/-- Extension of scalars along a ring homomorphism `f : R →+* S` sends projective modules to
projective modules: `extendScalars f` is left adjoint to `restrictScalars f`, and restriction of
scalars preserves epimorphisms. -/
theorem projective_extendScalars_obj {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} R) [Projective M] :
    Projective ((ModuleCat.extendScalars f).obj M) :=
  (ModuleCat.extendRestrictScalarsAdj f).map_projective M ‹Projective M›

theorem isKProjective_baseChangeComplexFunctor {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (K : CochainComplex (ModuleCat.{u} A) ℤ) (d : ℤ) [K.IsStrictlyLE d]
    [hproj : ∀ n, CategoryTheory.Projective (K.X n)] :
    CochainComplex.IsKProjective
      ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).obj K) := by
  -- the base-changed complex is still strictly bounded above by `d`
  have hle : ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).obj K).IsStrictlyLE d := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    dsimp only [Work.DSG4a.baseChangeComplexFunctor]
    rw [Functor.mapHomologicalComplex_obj_X]
    exact Functor.map_isZero _ (K.isZero_of_isStrictlyLE d i hi)
  -- and each of its terms is projective over `A'`
  have hproj' : ∀ n, Projective
      (((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).obj K).X n) := by
    intro n
    dsimp only [Work.DSG4a.baseChangeComplexFunctor]
    rw [Functor.mapHomologicalComplex_obj_X]
    exact CategoryTheory.Adjunction.map_projective
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A A')) (K.X n) (hproj n)
  exact @CochainComplex.isKProjective_of_projective _ _ _ _ d hle hproj'

end Work.DSG4a
