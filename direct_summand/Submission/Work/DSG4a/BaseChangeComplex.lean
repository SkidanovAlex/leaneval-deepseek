import Mathlib
import Submission.Work.DSMap.Map

/-!
# DSG4a: base change of cochain complexes of modules

The transport of a finite free model `P` of `RΓ(X, 𝒪)` from `A` to an `A`-algebra `A'`
(the hypothesis `hbc` of `area_G4a_localGlobal_of_models`, see `NOTES.md`) is the base change of
a complex: terms `A' ⊗[A] K.X n` with the differentials `1 ⊗ d`.  This is
`Functor.mapHomologicalComplex` applied to `ModuleCat.extendScalars (algebraMap A A')`.

For the application one needs: (i) if `K` is a bounded-above complex of free (hence projective)
`A`-modules then the base change is K-projective over `A'`; (ii) if `A → A'` is flat then the
base change functor is exact, hence preserves quasi-isomorphisms.  These are
`isKProjective_baseChangeComplexFunctor` and `quasiIso_baseChangeComplexFunctor` below.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG4a

/-- The **base change functor** on cochain complexes of modules along an algebra map
`A → A'`. -/
noncomputable def baseChangeComplexFunctor {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] : CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} A') ℤ :=
  Functor.mapHomologicalComplex (ModuleCat.extendScalars (algebraMap A A')) (ComplexShape.up ℤ)

/-- The base change of a cochain complex of `A`-modules to an `A`-algebra `A'`. -/
noncomputable abbrev baseChangeComplex {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (K : CochainComplex (ModuleCat.{u} A) ℤ) : CochainComplex (ModuleCat.{u} A') ℤ :=
  (baseChangeComplexFunctor (A := A) (A' := A')).obj K

end Work.DSG4a
