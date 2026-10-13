import Mathlib
import Submission.Work.DSMap.Mix2Fix

/-!
# `phiU` is of finite type over affine opens

For a proper morphism `f : X ⟶ Spec A` and an affine open `U ⊆ X`, the structure map
`A → Γ(X, U)` given by `DSMap.phiU A X f U` (the composite of the `A`-algebra structure on
global sections with restriction) is a morphism of finite type. This is the local finite type
of `f` (`LocallyOfFiniteType`) transported across the identification of `phiU` with the
localized structure map `f.appLE`.
-/

universe u

namespace Work.DSM8m2.Chart

open CategoryTheory AlgebraicGeometry

/-- The `A`-algebra structure on `Γ(X, ⊤)` coming from the `Γ ⊣ Spec` adjunction equals
`f.appTop` after transporting along `ΓSpecIso.inv`. -/
private lemma phi_eq_appTop (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) :
    DSMap.phi A X f =
      (f.appTop).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) := by
  rw [DSMap.phi]
  rw [show (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))).symm f =
      Scheme.Γ.rightOp.map f ≫
        (ΓSpec.adjunction.counit.app (Opposite.op (CommRingCat.of A))) from
    Adjunction.homEquiv_counit ΓSpec.adjunction X (Opposite.op (CommRingCat.of A)) f]
  rw [unop_comp, ΓSpec.adjunction_counit_app]
  rw [CommRingCat.hom_comp]
  rw [show (Scheme.Γ.rightOp.map f).unop = Scheme.Hom.appTop f from by
    rw [Functor.rightOp_map]; rfl]
  rfl

theorem finiteType_phiU {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) [AlgebraicGeometry.IsProper f]
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ k, AlgebraicGeometry.IsAffineOpen (U k)) (k : ι) :
    RingHom.FiniteType (DSMap.phiU A X f (U k)) := by
  have hphi := phi_eq_appTop A f
  -- `f` is locally of finite type, hence so is its map on the affine chart `U k`.
  have hfin : ((f.appLE (⊤ : (Spec (.of A)).Opens) (U k) le_top).hom).FiniteType :=
    LocallyOfFiniteType.finiteType_appLE f (isAffineOpen_top _) (hU k) le_top
  -- The `ΓSpecIso` is an isomorphism, hence of finite type.
  have h_inv : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).FiniteType := by
    apply RingHom.FiniteType.of_surjective
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).surjective
  -- Identify `phiU` with the chart map precomposed with `ΓSpecIso.inv`.
  have hEq : DSMap.phiU A X f (U k) =
      (f.appLE (⊤ : (Spec (.of A)).Opens) (U k) le_top).hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) := by
    rw [DSMap.phiU, hphi]
    simp only [Scheme.Hom.appLE]
    rw [CommRingCat.hom_comp]
    rw [← RingHom.comp_assoc]
    rfl
  rw [hEq]
  exact RingHom.FiniteType.comp hfin h_inv

end Work.DSM8m2.Chart
