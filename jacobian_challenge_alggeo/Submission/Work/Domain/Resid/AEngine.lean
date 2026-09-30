/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RESID (area DM): the valuation-ring engine (definitions)

This file contains the objects by which the residue map `σ : X ⤏ Sym^m C` is fed from the
valuations of the function field of `X`:

* `canonAlgebra`: for a ring homomorphism `ρ : 𝒪_{X,x} →+* A`, the `K`-algebra structure on `A`
  which makes the composite `Spec A ⟶ Spec 𝒪_{X,x} ⟶ X` a morphism over `Spec K`;
* `canonPt`: the canonical `A`-point of `X`, `Spec A ⟶ Spec 𝒪_{X,x} ⟶ X`;
* `canonResAlgebra`: the corresponding `K`-algebra structure on the residue field of `A`;
* `residueAlgHom`: the induced map of residue fields `κ(x) ⟶ κ(A)`.

The *properties* of these objects (their generic and closed fibres) are proved in the files
`Resid/CanonPt*.lean` of this area.
-/
import Submission.Work.Domain.Resid.Gen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.Domain.Resid

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} [SpecLin.DivBase C]
variable {X : Sch K}

noncomputable section

/-! ## The canonical point of a valuation subring -/

/-- The `K`-algebra structure on a `K`-ring `A` which makes the canonical morphism
`Spec A ⟶ Spec 𝒪_{X,x} ⟶ X` (for a ring homomorphism `ρ : 𝒪_{X,x} →+* A`) a morphism over
`Spec K`.  It is defined by pulling back the composite `Spec A ⟶ Spec K` along `Spec`. -/
def canonAlgebra (x : X.left) {A : Type u} [CommRing A]
    (ρ : X.left.presheaf.stalk x →+* A) : Algebra K A :=
  (Spec.preimage (Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x ≫ X.hom)).hom.toAlgebra

/-- The structure morphism of `specOf K A` for the canonical `K`-algebra structure on `A`. -/
theorem canonAlgebra_spec (x : X.left) {A : Type u} [CommRing A]
    (ρ : X.left.presheaf.stalk x →+* A) :
    letI := canonAlgebra (K := K) x ρ
    (specOf K A).hom = Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x ≫ X.hom := by
  letI := canonAlgebra (K := K) x ρ
  rw [specOf_hom]
  rw [show CommRingCat.ofHom (algebraMap K A) =
    Spec.preimage (Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x ≫ X.hom) from rfl]
  exact Spec.map_preimage _

/-- **The canonical `A`-point of `X`**: for a ring homomorphism `ρ : 𝒪_{X,x} →+* A` which is a
morphism over `K` (that is, `hKA` holds), the composite `Spec A ⟶ Spec 𝒪_{X,x} ⟶ X`. -/
def canonPt (x : X.left) {A : Type u} [CommRing A] [Algebra K A]
    (ρ : X.left.presheaf.stalk x →+* A)
    (hKA : (specOf K A).hom = Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x ≫
      X.hom) : RPt X A :=
  Over.homMk (Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x)
    (by rw [Category.assoc]; exact hKA.symm)

@[simp]
theorem canonPt_left (x : X.left) {A : Type u} [CommRing A] [Algebra K A]
    (ρ : X.left.presheaf.stalk x →+* A)
    (hKA : (specOf K A).hom = Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x ≫
      X.hom) :
    (canonPt x ρ hKA).left = Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x := rfl

/-- The `K`-algebra structure on the residue field of a local `K`-ring `A`, transported along
`Spec (residue) : Spec κ(A) ⟶ Spec A`. -/
def canonResAlgebra (x : X.left) {A : Type u} [CommRing A] [IsLocalRing A]
    (ρ : X.left.presheaf.stalk x →+* A) : Algebra K (IsLocalRing.ResidueField A) :=
  (Spec.preimage (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
    Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x ≫ X.hom)).hom.toAlgebra

/-- The structure morphism of `specOf K κ(A)` for the canonical `K`-algebra structure on the
residue field of `A`. -/
theorem canonResAlgebra_spec (x : X.left) {A : Type u} [CommRing A] [IsLocalRing A]
    (ρ : X.left.presheaf.stalk x →+* A) :
    letI := canonResAlgebra (K := K) x ρ
    (specOf K (IsLocalRing.ResidueField A)).hom =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
        Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x ≫ X.hom := by
  letI := canonResAlgebra (K := K) x ρ
  rw [specOf_hom]
  rw [show CommRingCat.ofHom (algebraMap K (IsLocalRing.ResidueField A)) =
    Spec.preimage (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
      Spec.map (CommRingCat.ofHom ρ) ≫ X.left.fromSpecStalk x ≫ X.hom) from rfl]
  exact Spec.map_preimage _

/-- The induced map of residue fields `κ(x) ⟶ κ(A)`. -/
def residueAlgHom (x : X.left) {A : Type u} [CommRing A] [IsLocalRing A]
    (ρ : X.left.presheaf.stalk x →+* A) [IsLocalHom ((IsLocalRing.residue A).comp ρ)] :
    IsLocalRing.ResidueField (X.left.presheaf.stalk x) →+* IsLocalRing.ResidueField A :=
  IsLocalRing.ResidueField.lift ((IsLocalRing.residue A).comp ρ)

/-- The defining property of `residueAlgHom`: it is the factorization of `ρ` followed by the
residue map through the residue field of `𝒪_{X,x}`. -/
theorem residueAlgHom_comp (x : X.left) {A : Type u} [CommRing A] [IsLocalRing A]
    (ρ : X.left.presheaf.stalk x →+* A) [IsLocalHom ((IsLocalRing.residue A).comp ρ)] :
    (residueAlgHom x ρ).comp (IsLocalRing.residue (X.left.presheaf.stalk x)) =
      (IsLocalRing.residue A).comp ρ :=
  IsLocalRing.ResidueField.lift_comp_residue _

end

end Work.Domain.Resid
