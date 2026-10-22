import Mathlib

/-!
# The free light condensed module functor preserves monomorphisms

We show that a monomorphism `T ⟶ T'` of light condensed sets induces a monomorphism
`ℤ[T] ⟶ ℤ[T']` of light condensed abelian groups.

The free light condensed `ℤ`-module functor is
`free ℤ = sheafToPresheaf ⋙ whiskerRight (ModuleCat.free ℤ) ⋙ presheafToSheaf`
(definitionally, `Mathlib.Condensed.Light.Module` defines `LightCondensed.free R` as
`Sheaf.composeAndSheafify _ (ModuleCat.free R)`). Each of the three factors preserves
monomorphisms:

* `sheafToPresheaf` is a right adjoint, hence preserves limits, hence monomorphisms;
* `whiskerRight (ModuleCat.free ℤ)` preserves monomorphisms because postcomposition with a
  functor preserving monomorphisms does (monomorphisms in a functor category are computed
  pointwise), and `ModuleCat.free ℤ` sends injective maps of types to injective linear maps
  (a finitely supported function is determined by its images under an injective map);
* `presheafToSheaf` is left exact (sheafification preserves finite limits), hence preserves
  monomorphisms.

Along the way we record that a monomorphism of sheaves is exactly a monomorphism of the
underlying presheaf morphisms (`Sheaf.Hom.mono_iff_presheaf_mono`), so the hypothesis
`Mono φ.hom` of the statement is precisely `Mono φ`.
-/

namespace Work.CONDMV.FreeMono

open CategoryTheory

set_option linter.style.haveILetI false

/-- The free module functor `Type u ⥤ ModuleCat R` preserves monomorphisms: an injective map of
types induces an injective linear map between the corresponding free modules. -/
theorem moduleCatFree_preservesMonomorphisms (R : Type) [Ring R] :
    Functor.PreservesMonomorphisms (ModuleCat.free R) where
  preserves {X Y} f hf := by
    rw [ModuleCat.mono_iff_injective]
    have hf' : Function.Injective f := (mono_iff_injective f).1 hf
    intro l l' h
    change Finsupp.mapDomain f l = Finsupp.mapDomain f l' at h
    exact Finsupp.mapDomain_injective hf' h

/-- The free light condensed `ℤ`-module functor preserves monomorphisms. -/
theorem free_preservesMonomorphisms :
    Functor.PreservesMonomorphisms (LightCondensed.free ℤ) := by
  haveI := moduleCatFree_preservesMonomorphisms ℤ
  unfold LightCondensed.free
  infer_instance

theorem mono_free_map {T T' : LightCondSet.{0}} (φ : T ⟶ T')
    (h : CategoryTheory.Mono φ.hom) :
    CategoryTheory.Mono ((LightCondensed.free ℤ).map φ) := by
  haveI : Mono φ :=
    Sheaf.Hom.mono_of_presheaf_mono (coherentTopology LightProfinite) (Type 0) φ (h := h)
  exact free_preservesMonomorphisms.preserves φ

end Work.CONDMV.FreeMono
