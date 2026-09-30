/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GCBasics — shared conventions of the Jacobian drive

This is area **GB**: the chapter that fixes the vocabulary every other area of the
Jacobian drive uses.  It is deliberately thin, and depends only on Mathlib and on
area CB (`Submission/Work/CurveBasics`).

## The conventions

* `Work.GCBasics.Sch K` is the category of `K`-schemes: `Over (Spec K)`.  This is
  definitionally the `Sch k` of `Work.AbVar` and the `Over (Spec (.of k))` of the
  challenge statement.
* `specOf K R` is `Spec R` as a `K`-scheme, for a `K`-algebra `R`.
* `RPt X R` are the `R`-valued points of `X`, for `R` a `K`-algebra; `FPt X F` is the
  case of a field.
* `RPt.map e` is precomposition with `Spec.map e`, so that a field extension
  `e : F →ₐ[K] F'` acts on points.
* `RPt.LandsIn p U` says that the *closed point* of `Spec R` is mapped into the open
  subscheme `U`.  For `R` local this is equivalent to `p` factoring through `U`
  (`RPt.factor_of_closed_landsIn`).
* `resField X x`, `resPt X x` are the residue field of a point and the canonical
  `κ(x)`-point of `X`; `genPt R` and `closedPt R` are the generic point of a domain
  and the closed point of a local ring, as points of `Spec R`.
* `Opens.toOver U` and `Opens.ιOver U` turn an open subscheme of a `K`-scheme into a
  `K`-scheme again, with its inclusion.
* `Dominates A x` says that the valuation subring `A` of the function field dominates
  the local ring `O_{X,x}`.

The module `Work.GCBasics.GC` re-exports the same names in the namespace `Work.GC`,
which is how the lead's notes write them.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-- The category of `K`-schemes. -/
abbrev Sch (K : Type u) [Field K] : Type (u + 1) := Over (Spec (CommRingCat.of K))

/-- `Spec R`, as an object of `Sch K`, for `R` a `K`-algebra. -/
abbrev specOf (K : Type u) [Field K] (R : Type u) [CommRing R] [Algebra K R] : Sch K :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R)))

/-- The structure morphism of `specOf K R`. -/
theorem specOf_hom (K : Type u) [Field K] (R : Type u) [CommRing R] [Algebra K R] :
    (specOf K R).hom = Spec.map (CommRingCat.ofHom (algebraMap K R)) := rfl

/-- `R`-valued points of a `K`-scheme, for `R` a `K`-algebra. -/
abbrev RPt (X : Sch K) (R : Type u) [CommRing R] [Algebra K R] : Type u := specOf K R ⟶ X

/-- `F`-valued points of a `K`-scheme, for `F` a field extension of `K`. -/
abbrev FPt (X : Sch K) (F : Type u) [Field F] [Algebra K F] : Type u := RPt X F

/-- The morphism `Spec R' ⟶ Spec R` induced by a `K`-algebra homomorphism, as a morphism
of `K`-schemes. -/
def specOfMap {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
    (e : R →ₐ[K] R') : specOf K R' ⟶ specOf K R :=
  Over.homMk (Spec.map (CommRingCat.ofHom e.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K R)) =
        Spec.map (CommRingCat.ofHom (algebraMap K R'))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext x
    exact e.commutes x)

@[simp]
theorem specOfMap_left {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
    (e : R →ₐ[K] R') :
    (specOfMap (K := K) e).left = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

/-- Precomposition with the morphism of spectra induced by a `K`-algebra homomorphism:
a field extension `F → F'` acts on the points of a `K`-scheme. -/
def RPt.map {X : Sch K} {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R']
    [Algebra K R'] (e : R →ₐ[K] R') (p : RPt X R) : RPt X R' := specOfMap e ≫ p

@[simp]
theorem specOfMap_id (R : Type u) [CommRing R] [Algebra K R] :
    specOfMap (K := K) (AlgHom.id K R) = 𝟙 (specOf K R) := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (AlgHom.id K R).toRingHom) = 𝟙 (Spec (CommRingCat.of R))
  rw [show (AlgHom.id K R).toRingHom = RingHom.id R from rfl,
    show CommRingCat.ofHom (RingHom.id R) = 𝟙 (CommRingCat.of R) from rfl, Spec.map_id]

@[simp]
theorem RPt.map_id {X : Sch K} {R : Type u} [CommRing R] [Algebra K R] (p : RPt X R) :
    RPt.map (AlgHom.id K R) p = p := by
  simp [RPt.map]

theorem specOfMap_comp {R R' R'' : Type u} [CommRing R] [Algebra K R] [CommRing R']
    [Algebra K R'] [CommRing R''] [Algebra K R''] (e : R →ₐ[K] R') (e' : R' →ₐ[K] R'') :
    specOfMap (K := K) (e'.comp e) = specOfMap e' ≫ specOfMap (K := K) e := by
  apply Over.OverMorphism.ext
  rw [specOfMap_left, Over.comp_left, specOfMap_left, specOfMap_left, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  ext x
  rfl

theorem RPt.map_comp {X : Sch K} {R R' R'' : Type u} [CommRing R] [Algebra K R]
    [CommRing R'] [Algebra K R'] [CommRing R''] [Algebra K R''] (e : R →ₐ[K] R')
    (e' : R' →ₐ[K] R'') (p : RPt X R) :
    RPt.map (e'.comp e) p = RPt.map e' (RPt.map e p) := by
  simp only [RPt.map, specOfMap_comp, Category.assoc]

namespace RPt

variable {X : Sch K}

/-- A point of `Spec R` (with `R` local) *lands in* an open subscheme `U ⊆ X` if the closed
point of `Spec R` is mapped into `U`.  For `R` local this is equivalent to the point
factoring through `U`, see `RPt.factor_of_closed_landsIn`. -/
def LandsIn {R : Type u} [CommRing R] [Algebra K R] [IsLocalRing R]
    (p : RPt X R) (U : X.left.Opens) : Prop := p.left (IsLocalRing.closedPoint R) ∈ U

variable {R : Type u} [CommRing R] [Algebra K R] [IsLocalRing R] (p : RPt X R)

theorem landsIn_iff (U : X.left.Opens) :
    p.LandsIn U ↔ p.left (IsLocalRing.closedPoint R) ∈ U := Iff.rfl

theorem landsIn_preimage {Y : Sch K} (f : X ⟶ Y) (V : Y.left.Opens) :
    RPt.LandsIn (p ≫ f) V ↔ p.LandsIn (f.left ⁻¹ᵁ V) := Iff.rfl

@[simp]
theorem landsIn_top : p.LandsIn (⊤ : X.left.Opens) := trivial

@[simp]
theorem not_landsIn_bot : ¬ p.LandsIn (⊥ : X.left.Opens) := fun h => h

theorem LandsIn.mono {U V : X.left.Opens} (hUV : U ≤ V) (h : p.LandsIn U) : p.LandsIn V :=
  hUV h

end RPt

namespace FPt

variable {X : Sch K}

/-- `FPt.LandsIn` is `RPt.LandsIn`: the closed point of `Spec F` (the unique point of
`Spec F`, `F` a field) is mapped into `U`. -/
abbrev LandsIn {F : Type u} [Field F] [Algebra K F] (p : FPt X F) (U : X.left.Opens) : Prop :=
  RPt.LandsIn p U

end FPt

/-- The underlying scheme of an object of `Sch K` is a scheme over `Spec K`.  This is the
scoped bridge that lets us use Mathlib's `RationalMap`/`PartialMap` theory (whose statements
are phrased with the `X.Over S` typeclass) on `K`-schemes.  Open the scope with
`open scoped Work.GCBasics` to use it. -/
scoped instance overClass (X : Sch K) : X.left.Over (Spec (CommRingCat.of K)) := ⟨X.hom⟩

/-- The residue field of a point of a `K`-scheme (as a type). -/
abbrev resField (X : Sch K) (x : X.left) : Type u := X.left.residueField x

instance resFieldField (X : Sch K) (x : X.left) : Field (resField X x) := inferInstance

/-- The residue field of a point, as a `K`-algebra.  It is defined by pulling back along
`Spec.map`, so that `specOf_resField_hom` holds by construction. -/
instance resFieldAlgebra (X : Sch K) (x : X.left) : Algebra K (resField X x) :=
  (Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom)).hom.toAlgebra

theorem specOf_resField_hom (X : Sch K) (x : X.left) :
    (specOf K (resField X x)).hom = X.left.fromSpecResidueField x ≫ X.hom := by
  rw [specOf_hom]
  rw [show CommRingCat.ofHom (algebraMap K (X.left.residueField x)) =
      Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom) from rfl]
  exact Spec.map_preimage _

/-- The canonical `κ(x)`-point of a `K`-scheme `X` at a point `x`. -/
def resPt (X : Sch K) (x : X.left) : FPt X (resField X x) :=
  Over.homMk (X.left.fromSpecResidueField x) (specOf_resField_hom X x).symm

@[simp]
theorem resPt_left (X : Sch K) (x : X.left) : (resPt X x).left = X.left.fromSpecResidueField x :=
  rfl

@[simp]
theorem resPt_apply (X : Sch K) (x : X.left) (s : Spec (CommRingCat.of (resField X x))) :
    (resPt X x).left s = x := by
  rw [resPt_left]
  exact Scheme.fromSpecResidueField_apply x s

/-- The canonical `κ(x)`-point of `X` lands in an open subscheme `U` exactly when `x ∈ U`. -/
theorem resPt_landsIn_iff (X : Sch K) (x : X.left) (U : X.left.Opens) :
    RPt.LandsIn (resPt X x) U ↔ x ∈ U := by
  rw [RPt.landsIn_iff, resPt_left]
  have h : (Over.left X).fromSpecResidueField x (IsLocalRing.closedPoint (resField X x)) = x :=
    Scheme.fromSpecResidueField_apply x _
  rw [h]

/-- The generic point of `Spec R`, as a point of `Spec R` over `Frac R` (`R` a domain). -/
def genPt (R : Type u) [CommRing R] [IsDomain R] [Algebra K R] :
    FPt (specOf K R) (FractionRing R) :=
  specOfMap (K := K) (IsScalarTower.toAlgHom K R (FractionRing R))

/-- The closed point of `Spec R`, as a point of `Spec R` over `R ⧸ m` (`R` local). -/
def closedPt (R : Type u) [CommRing R] [IsLocalRing R] [Algebra K R] :
    FPt (specOf K R) (IsLocalRing.ResidueField R) :=
  specOfMap (K := K)
    { toRingHom := IsLocalRing.residue R
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_eq K R (IsLocalRing.ResidueField R)]
        rfl }

/-- An open subscheme of a `K`-scheme, as a `K`-scheme. -/
abbrev Opens.toOver {X : Sch K} (U : X.left.Opens) : Sch K := Over.mk (U.ι ≫ X.hom)

/-- The inclusion of an open subscheme of a `K`-scheme into the ambient `K`-scheme. -/
def Opens.ιOver {X : Sch K} (U : X.left.Opens) : Opens.toOver U ⟶ X :=
  Over.homMk U.ι rfl

@[simp]
theorem Opens.ιOver_left {X : Sch K} (U : X.left.Opens) : (Opens.ιOver U).left = U.ι := rfl

/-- The underlying set of the image of the inclusion of an open subscheme. -/
theorem Opens.range_ιOver {X : Sch K} (U : X.left.Opens) :
    Set.range (Opens.ιOver U).left = (U : Set X.left) := Scheme.Opens.range_ι U

instance Opens.isOpenImmersion_ιOver {X : Sch K} (U : X.left.Opens) :
    IsOpenImmersion (Opens.ιOver U).left := inferInstanceAs (IsOpenImmersion U.ι)

/-- The function field of an integral `K`-scheme, as a `K`-algebra: the structure morphism
`Spec K(X) ⟶ X` of the generic point, pushed to `Spec K`. -/
instance functionFieldAlgebra (X : Sch K) [IsIntegral X.left] : Algebra K X.left.functionField :=
  (Spec.preimage (X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom)).hom.toAlgebra

theorem specOf_functionField_hom (X : Sch K) [IsIntegral X.left] :
    (specOf K X.left.functionField).hom =
      X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom := by
  rw [specOf_hom]
  rw [show CommRingCat.ofHom (algebraMap K X.left.functionField) =
      Spec.preimage (X.left.fromSpecStalk (genericPoint X.left) ≫ X.hom) from rfl]
  exact Spec.map_preimage _

/-- The generic point of an integral `K`-scheme, as a point over its function field. -/
def genericFPt (X : Sch K) [IsIntegral X.left] : FPt X X.left.functionField :=
  Over.homMk (X.left.fromSpecStalk (genericPoint X.left)) (specOf_functionField_hom X).symm

/-- The generic point of an integral `K`-scheme is the image of the closed point of
`Spec K(X)` under `genericFPt`. -/
@[simp]
theorem genericFPt_apply (X : Sch K) [IsIntegral X.left] :
    (genericFPt X).left (IsLocalRing.closedPoint X.left.functionField) = genericPoint X.left :=
  Scheme.fromSpecStalk_closedPoint

theorem genericFPt_landsIn_iff (X : Sch K) [IsIntegral X.left] (U : X.left.Opens) :
    RPt.LandsIn (genericFPt X) U ↔ genericPoint X.left ∈ U := by
  rw [RPt.landsIn_iff, genericFPt_apply]

/-- A valuation subring `A` of the function field of an integral scheme `X` *dominates* the
local ring at `x` if the germ map `O_{X,x} → K(X)` lands in `A` and is a local homomorphism,
i.e. if `A` contains `O_{X,x}` and its maximal ideal. -/
def Dominates {X : Scheme.{u}} [IsIntegral X] (A : ValuationSubring X.functionField)
    (x : X) : Prop :=
  ∃ h : ∀ r : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField r ∈ A.toSubring,
    IsLocalHom ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict A.toSubring h)

end

end Work.GCBasics
