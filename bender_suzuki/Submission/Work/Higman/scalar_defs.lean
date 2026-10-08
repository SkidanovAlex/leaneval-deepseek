/-
Copyright (c) 2024. All rights reserved.

# Vocabulary for the module form of the type-`B` scalar dichotomy

`Work.Higman.scalar_module_of_layers` proves that a finite `𝔽₂`-vector space `V` carrying a
linear endomorphism `σ` of order `q - 1`, fixed-point-free on `V \ {0}`, with `|V| = q ^ 2` and
with at least `q + 1` `σ`-invariant subspaces of cardinality `q`, is (as a `𝔽₂[σ]`-module) the
square of a field of order `q` on which `σ` acts as a scalar.

This file fixes the vocabulary used by that proof and by the lemmas it is assembled from:

* `Work.Higman.Inv` — a subspace is `σ`-invariant;
* `Work.Higman.SimpleMod` — a non-zero invariant subspace with no proper non-zero invariant
  subspace;
* `Work.Higman.restr` — the restriction of `σ` to an invariant subspace;
* `Work.Higman.EqvIso` — a `σ`-equivariant linear equivalence between two invariant subspaces.
-/

import Mathlib
import Submission.Work.Higman.exists_singer_iso

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A subspace `U` of `V` is invariant under the linear endomorphism `σ`. -/
def Inv (σ : V →ₗ[ZMod 2] V) (U : Submodule (ZMod 2) V) : Prop := ∀ v ∈ U, σ v ∈ U

/-- `U` is a `σ`-simple (irreducible) subspace: it is non-zero, invariant, and has no proper
non-zero invariant subspace. -/
def SimpleMod (σ : V →ₗ[ZMod 2] V) (U : Submodule (ZMod 2) V) : Prop :=
  Inv σ U ∧ U ≠ ⊥ ∧
    ∀ W : Submodule (ZMod 2) V, W ≤ U → Inv σ W → W = ⊥ ∨ W = U

/-- The restriction of `σ` to an invariant subspace. -/
def restr (σ : V →ₗ[ZMod 2] V) {U : Submodule (ZMod 2) V} (h : Inv σ U) : U →ₗ[ZMod 2] U :=
  σ.restrict h

@[simp]
lemma restr_apply (σ : V →ₗ[ZMod 2] V) {U : Submodule (ZMod 2) V} (h : Inv σ U) (x : U) :
    (restr σ h x : V) = σ x := rfl

@[simp]
lemma restr_apply_coe (σ : V →ₗ[ZMod 2] V) {U : Submodule (ZMod 2) V} (h : Inv σ U) (x : U) :
    restr σ h x = ⟨σ x.1, h x.1 x.2⟩ := rfl

/-- A `σ`-equivariant linear equivalence between two invariant subspaces: an isomorphism of
`𝔽₂[σ]`-modules. -/
def EqvIso (σ : V →ₗ[ZMod 2] V) (S T : Submodule (ZMod 2) V) : Prop :=
  ∃ (hS : Inv σ S) (hT : Inv σ T) (e : S ≃ₗ[ZMod 2] T),
    ∀ x : S, e (restr σ hS x) = restr σ hT (e x)

lemma Inv.bot (σ : V →ₗ[ZMod 2] V) : Inv σ (⊥ : Submodule (ZMod 2) V) := by
  intro v hv
  rw [Submodule.mem_bot] at hv ⊢
  rw [hv, map_zero]

lemma Inv.top (σ : V →ₗ[ZMod 2] V) : Inv σ (⊤ : Submodule (ZMod 2) V) := fun _ _ => trivial

lemma Inv.inf {σ : V →ₗ[ZMod 2] V} {U W : Submodule (ZMod 2) V}
    (hU : Inv σ U) (hW : Inv σ W) : Inv σ (U ⊓ W) := by
  intro v hv
  rw [Submodule.mem_inf] at hv ⊢
  exact ⟨hU v hv.1, hW v hv.2⟩

end Work.Higman
