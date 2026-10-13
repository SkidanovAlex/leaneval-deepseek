import Mathlib
import Submission.Work.DSG4a.BaseChangeComplex

/-!
# DSG4a: flat base change preserves quasi-isomorphisms

If `A → A'` is a flat ring homomorphism, then extension of scalars `A' ⊗[A] –` is an exact
functor between the abelian categories of modules: it preserves finite colimits because it is a
left adjoint (its right adjoint being restriction of scalars), and it preserves finite limits
because `A'` is flat over `A`.  A functor between abelian categories that preserves homology
carries quasi-isomorphisms to quasi-isomorphisms, and `baseChangeComplexFunctor` is precisely
the functor induced by extension of scalars on cochain complexes.
-/

open CategoryTheory Limits

universe u u₁ u₂ u₃

namespace Work.DSG4a

/-- Extension of scalars is an additive functor.  Mathlib has the monoidal structure on
`ModuleCat.extendScalars` but not the additivity of the induced maps on morphisms (it is the
additivity of `LinearMap.baseChange`). -/
instance extendScalars_additive {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    (f : R →+* S) : (ModuleCat.extendScalars.{u₁, u₂, u₃} f).Additive where
  map_add := by
    intro M N g h
    simp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map', ModuleCat.hom_add,
      LinearMap.baseChange_add]
    exact (ModuleCat.ofHom_add _ _).symm

theorem quasiIso_baseChangeComplexFunctor {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (hflat : Module.Flat A A') {K L : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso ((Work.DSG4a.baseChangeComplexFunctor (A := A) (A' := A')).map f) := by
  -- Flatness of `A'` over `A` is flatness of the ring homomorphism `algebraMap A A'`.
  have hf' : (algebraMap A A').Flat := RingHom.flat_algebraMap_iff.mpr hflat
  -- `A' ⊗[A] –` preserves finite limits (flatness) and finite colimits (left adjoint).
  have hlim : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A A')) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf'
  have hcolim : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A A')) :=
    inferInstance
  have hhom : (ModuleCat.extendScalars.{u, u, u} (algebraMap A A')).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have hadd : (ModuleCat.extendScalars.{u, u, u} (algebraMap A A')).Additive := inferInstance
  have := hf
  have := hlim
  have := hcolim
  have := hhom
  have := hadd
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f
    (ModuleCat.extendScalars (algebraMap A A'))

end Work.DSG4a
