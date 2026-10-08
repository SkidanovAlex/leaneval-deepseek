/-
Copyright (c) 2024. All rights reserved.

# Shared vocabulary for the layer dichotomy

`Work.Higman.layers_card_dichotomy` counts the `ξ`-invariant layers `Z(P) ≤ M ≤ P` of order `q ^ 2`
in a Suzuki 2-group `P` of order `q ^ 3`.  The count is carried out on `V = P / Z(P)`, an
`𝔽₂`-vector space of order `q ^ 2` carrying the linear automorphism `σ` induced by `ξ`; layers
correspond to `σ`-invariant subspaces of `V` of `𝔽₂`-dimension `n` (`q = 2 ^ n`).

This file fixes the vocabulary used by the files

* `Submission.Work.Higman.Layers.orbit_count`,
* `Submission.Work.Higman.Layers.card_lower_bound`,
* `Submission.Work.Higman.Layers.cyclic_minpoly`,
* `Submission.Work.Higman.Layers.two_constituents`,
* `Submission.Work.Higman.Layers.count_and_hom`,

and by `Submission.Work.Higman.layers_card_dichotomy` itself.
-/

import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Higman.Layers

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A subspace is invariant under `σ`. -/
def IsInv (σ : V →ₗ[ZMod 2] V) (U : Submodule (ZMod 2) V) : Prop := ∀ v ∈ U, σ v ∈ U

/-- `σ` is *semiregular* on the non-zero vectors: no non-trivial power of `σ` has a non-zero
fixed point. -/
def Semiregular (σ : V →ₗ[ZMod 2] V) : Prop :=
  ∀ k : ℕ, ∀ v : V, v ≠ 0 → (σ ^ k) v = v → σ ^ k = 1

/-- `C` is `σ`-simple: a non-zero invariant subspace with no proper non-zero invariant subspace. -/
def IsSimpleMod (σ : V →ₗ[ZMod 2] V) (C : Submodule (ZMod 2) V) : Prop :=
  IsInv σ C ∧ C ≠ ⊥ ∧ ∀ U : Submodule (ZMod 2) V, U ≤ C → IsInv σ U → U = ⊥ ∨ U = C

/-- The `𝔽₂[σ]`-span of `v`, i.e. the smallest `σ`-invariant subspace containing `v`. -/
def cycSpan (σ : V →ₗ[ZMod 2] V) (v : V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (Set.range fun k : ℕ => (σ ^ k) v)

/-- The restriction of `σ` to an invariant subspace. -/
def restrictInv (σ : V →ₗ[ZMod 2] V) (C : Submodule (ZMod 2) V) (hC : IsInv σ C) :
    C →ₗ[ZMod 2] C :=
  (σ.domRestrict C).codRestrict C fun x => hC x x.2

/-- The `σ`-equivariant linear maps `C₂ → C₁`. -/
def HomInv (σ : V →ₗ[ZMod 2] V) (C₂ C₁ : Submodule (ZMod 2) V) (hC₂ : IsInv σ C₂)
    (hC₁ : IsInv σ C₁) : Type _ :=
  {φ : C₂ →ₗ[ZMod 2] C₁ // ∀ y : C₂, φ (restrictInv σ C₂ hC₂ y) = restrictInv σ C₁ hC₁ (φ y)}

/-- The `σ`-equivariant endomorphisms of an invariant subspace. -/
def EndInv (σ : V →ₗ[ZMod 2] V) (C : Submodule (ZMod 2) V) (hC : IsInv σ C) : Type _ :=
  HomInv σ C C hC hC

/-- The set of `σ`-invariant subspaces of `𝔽₂`-dimension `n`. -/
def InvSubspaces (σ : V →ₗ[ZMod 2] V) (n : ℕ) : Type _ :=
  {U : Submodule (ZMod 2) V // IsInv σ U ∧ Module.finrank (ZMod 2) U = n}

end Work.Higman.Layers
