/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite group actions on schemes (area SY)

This file sets up the basic language of a group acting on a scheme by scheme automorphisms,
together with the data needed to form the quotient `X/G` by gluing the spectra of the rings of
invariants of `G`-invariant affine open subschemes.

## Main definitions

* `Work.SymQuot.GAction G X`: an action of a group `G` on a scheme `X` by automorphisms.
* `Work.SymQuot.GAction.IsInvariantOpen`: a `G`-invariant open subscheme.
* `Work.SymQuot.GAction.IsInvariantMorphism`: a `G`-invariant morphism.
* `Work.SymQuot.QuotientData`: the data needed to form the quotient `X/G`: an action, the
  fact that intersections of affine opens are affine, and the fact that every point lies in a
  `G`-invariant affine open.

## Implementation notes

The action is stored as a pair of maps `hom : G → (X ⟶ X)` and `inv : G → (X ⟶ X)` with
`hom g ≫ inv g = 𝟙 X` and `inv g ≫ hom g = 𝟙 X`, rather than as a map `G → X ≅ X`: in the
latter formulation the laws of the structure cannot be stated by applying the field (the
elaborator refuses to apply a function-valued field whose value is an `Iso`).  The
corresponding isomorphism is `GAction.iso`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u v

namespace Work.SymQuot

/-- An action of a group `G` on a scheme `X` by scheme automorphisms.  The composition law is
written in the "contravariant" order `hom (g * h) = hom h ≫ hom g`, so that the induced action on
the points of `X`, `g • x = hom g x`, is a genuine left action. -/
structure GAction (G : Type v) [Group G] (X : Scheme.{u}) where
  /-- The morphism attached to each group element. -/
  hom : G → (X ⟶ X)
  /-- The inverse of the morphism attached to each group element. -/
  inv : G → (X ⟶ X)
  /-- Left inverse law. -/
  hom_inv : ∀ g : G, hom g ≫ inv g = 𝟙 X
  /-- Right inverse law. -/
  inv_hom : ∀ g : G, inv g ≫ hom g = 𝟙 X
  /-- The morphism attached to `1` is the identity. -/
  hom_one : hom 1 = 𝟙 X
  /-- The composition law. -/
  hom_mul : ∀ g h : G, hom (g * h) = hom h ≫ hom g

namespace GAction

variable {G : Type v} [Group G] {X : Scheme.{u}}

/-- The automorphism of `X` attached to a group element. -/
def iso (A : GAction G X) (g : G) : X ≅ X where
  hom := A.hom g
  inv := A.inv g
  hom_inv_id := A.hom_inv g
  inv_hom_id := A.inv_hom g

variable (A : GAction G X)

@[simp] lemma iso_hom (g : G) : (A.iso g).hom = A.hom g := rfl
@[simp] lemma iso_inv (g : G) : (A.iso g).inv = A.inv g := rfl

@[simp] lemma hom_one' : A.hom 1 = 𝟙 X := A.hom_one

@[simp] lemma hom_mul' (g h : G) : A.hom (g * h) = A.hom h ≫ A.hom g := A.hom_mul g h

lemma hom_mul_inv (g : G) : A.hom g⁻¹ ≫ A.hom g = 𝟙 X := by
  rw [← A.hom_mul g g⁻¹, mul_inv_cancel, A.hom_one]

lemma inv_hom_inv (g : G) : A.hom g ≫ A.hom g⁻¹ = 𝟙 X := by
  rw [← A.hom_mul g⁻¹ g, inv_mul_cancel, A.hom_one]

lemma inv_eq (g : G) : A.inv g = A.hom g⁻¹ := by
  calc A.inv g = 𝟙 X ≫ A.inv g := (Category.id_comp _).symm
    _ = (A.hom g⁻¹ ≫ A.hom g) ≫ A.inv g := by rw [hom_mul_inv A g]
    _ = A.hom g⁻¹ ≫ (A.hom g ≫ A.inv g) := Category.assoc _ _ _
    _ = A.hom g⁻¹ ≫ 𝟙 X := by rw [A.hom_inv]
    _ = A.hom g⁻¹ := Category.comp_id _

@[simp] lemma inv_one : A.inv 1 = 𝟙 X := by simp [inv_eq]

@[simp] lemma hom_inv_apply (g : G) : A.hom g⁻¹ = A.inv g := (inv_eq A g).symm

@[simp] lemma iso_inv_apply (g : G) : (A.iso g).inv = A.hom g⁻¹ := by
  rw [iso_inv, inv_eq]

/-- The induced action on the points of `X`, as a `MulAction` structure. -/
def toMulAction : MulAction G X where
  smul g x := A.hom g x
  one_smul x := by change A.hom 1 x = x; rw [A.hom_one]; rfl
  mul_smul g h x := by
    change A.hom (g * h) x = A.hom g (A.hom h x)
    rw [A.hom_mul]
    rfl

@[simp] lemma smul_def (g : G) (x : X) : A.toMulAction.smul g x = A.hom g x := rfl

end GAction

namespace GAction

variable {G : Type v} [Group G] {X : Scheme.{u}}

/-- The open subscheme `U` is `G`-invariant if it is stable under the action of every
`g : G`. -/
abbrev IsInvariantOpen (A : GAction G X) (U : X.Opens) : Prop := ∀ g : G, A.hom g ⁻¹ᵁ U = U

variable {A : GAction G X}

lemma isInvariantOpen_iff (A : GAction G X) (U : X.Opens) :
    A.IsInvariantOpen U ↔ ∀ (g : G) (x : X), A.hom g x ∈ U ↔ x ∈ U := by
  constructor
  · intro h g x
    have := congrArg (fun (V : X.Opens) => (x : X) ∈ (V : Set X)) (h g)
    simpa [Scheme.Hom.mem_preimage] using this
  · intro h g
    ext x
    simpa [Scheme.Hom.mem_preimage] using h g x

@[simp] lemma IsInvariantOpen.top : A.IsInvariantOpen ⊤ := by
  intro g
  rw [Scheme.Hom.preimage_top]

lemma IsInvariantOpen.inf {U V : X.Opens} (hU : A.IsInvariantOpen U)
    (hV : A.IsInvariantOpen V) : A.IsInvariantOpen (U ⊓ V) := by
  intro g
  rw [Scheme.Hom.preimage_inf, hU g, hV g]

lemma IsInvariantOpen.iSup {ι : Sort*} {U : ι → X.Opens}
    (hU : ∀ i, A.IsInvariantOpen (U i)) : A.IsInvariantOpen (⨆ i, U i) := by
  intro g
  rw [Scheme.Hom.preimage_iSup]
  exact iSup_congr fun i => hU i g

lemma IsInvariantOpen.mem_iff {U : X.Opens} (hU : A.IsInvariantOpen U) (g : G) (x : X) :
    A.hom g x ∈ U ↔ x ∈ U := (isInvariantOpen_iff A U).mp hU g x

lemma IsInvariantOpen.smul_mem {U : X.Opens} (hU : A.IsInvariantOpen U) {x : X} (hx : x ∈ U)
    (g : G) : A.hom g x ∈ U := (hU.mem_iff g x).mpr hx

/-- A morphism is `G`-invariant if it is invariant under precomposition with the action. -/
def IsInvariantMorphism (A : GAction G X) {Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ g : G, A.hom g ≫ f = f

lemma isInvariantMorphism_apply (A : GAction G X) {Y : Scheme.{u}} {f : X ⟶ Y}
    (h : A.IsInvariantMorphism f) (g : G) (x : X) : f (A.hom g x) = f x := by
  simpa using congr($(h g) x)

/-- The orbit of a point. -/
def orbit (A : GAction G X) (x : X) : Set X := {y | ∃ g : G, A.hom g x = y}

lemma mem_orbit_iff (A : GAction G X) {x y : X} :
    y ∈ A.orbit x ↔ ∃ g : G, A.hom g x = y := Iff.rfl

lemma mem_orbit_self (A : GAction G X) (x : X) : x ∈ A.orbit x :=
  ⟨1, by simp⟩

lemma orbit_eq_mulAction_orbit (A : GAction G X) (x : X) :
    A.orbit x = letI := A.toMulAction; MulAction.orbit G x := rfl

end GAction

end Work.SymQuot
