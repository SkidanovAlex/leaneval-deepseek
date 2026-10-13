import Mathlib

/-!
# DSG4a: extension of scalars commutes with finite products of modules

For a finite index type `α`, the categorical product `∏ᶜ M` in `ModuleCat A` is a finite
biproduct, and extension of scalars `A' ⊗[A] –` is an additive left adjoint, hence preserves
finite biproducts and therefore finite products.  The statement below records the resulting
isomorphism together with its compatibility with the projections, which is the form needed to
base-change a (finite) Čech model term by term.

The additivity of `ModuleCat.extendScalars` is not in Mathlib (it is the additivity of
`LinearMap.baseChange`), so we provide it here; the compatibility of additive functors with
finite biproducts is then derived from Mathlib's `IsBilimit.total` criterion, at the universe
level of `α` (Mathlib's `PreservesFiniteBiproducts` only covers index types in `Type 0`).
-/

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u u₁ u₂ v₁ v₂ w

set_option linter.style.haveILetI false

/-- Extension of scalars is an additive functor.  The additivity of the induced maps on morphisms
is the additivity of `LinearMap.baseChange`. -/
instance extendScalarsAdditivePi {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : (ModuleCat.extendScalars f).Additive where
  map_add := by
    intro M N g h
    simp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map', ModuleCat.hom_add,
      LinearMap.baseChange_add]
    exact (ModuleCat.ofHom_add _ _).symm

section

set_option backward.isDefEq.respectTransparency false
/-- An additive functor preserves biproducts indexed by any finite type (in an arbitrary
universe): pass to the `total` characterisation of bilimits, which additivity respects. -/
lemma preservesBiproduct_of_additive {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] {J : Type w}
    [Fintype J] (f : J → C) : PreservesBiproduct f F where
  preserves {b} hb := by
    exact ⟨isBilimitOfTotal _ (by
      simp_rw [F.mapBicone_π, F.mapBicone_ι, ← F.map_comp]
      erw [← F.map_sum, ← F.map_id, IsBilimit.total hb])⟩

end

theorem tensorPi_extendScalars {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] {α : Type u} [Fintype α] [DecidableEq α] (M : α → ModuleCat.{u} A) :
    ∃ e : (ModuleCat.extendScalars (algebraMap A A')).obj (∏ᶜ M) ≅
        ∏ᶜ (fun a => (ModuleCat.extendScalars (algebraMap A A')).obj (M a)),
      ∀ a : α, e.hom ≫ CategoryTheory.Limits.Pi.π (fun a =>
          (ModuleCat.extendScalars (algebraMap A A')).obj (M a)) a =
        (ModuleCat.extendScalars (algebraMap A A')).map (CategoryTheory.Limits.Pi.π M a) := by
  haveI : (ModuleCat.extendScalars (algebraMap A A')).Additive :=
    extendScalarsAdditivePi (algebraMap A A')
  haveI : PreservesBiproduct M (ModuleCat.extendScalars (algebraMap A A')) :=
    preservesBiproduct_of_additive _ M
  refine ⟨(ModuleCat.extendScalars (algebraMap A A')).mapIso (biproduct.isoProduct M).symm ≪≫
    Functor.mapBiproduct (ModuleCat.extendScalars (algebraMap A A')) M ≪≫
    biproduct.isoProduct (fun a => (ModuleCat.extendScalars (algebraMap A A')).obj (M a)), ?_⟩
  intro a
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [Iso.symm_hom, Functor.mapBiproduct_hom, biproduct.isoProduct_hom, biproduct.isoProduct_inv]
  simp only [Category.assoc]
  rw [Pi.lift_comp_π, biproduct.lift_π, ← Functor.map_comp, biproduct.lift_π]

end Work.DSG4a
