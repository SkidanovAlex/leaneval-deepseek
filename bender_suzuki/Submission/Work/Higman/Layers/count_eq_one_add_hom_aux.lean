/-
Copyright (c) 2024. All rights reserved.

# Auxiliary vocabulary for `Work.Higman.Layers.count_eq_one_add_hom`

This file only fixes the notion of the *graph* of a `σ`-equivariant map `C₂ → C₁` inside `V`,
used by the proof of `Work.Higman.Layers.count_eq_one_add_hom`.

If `V = C₁ ⊕ C₂` with `C₁, C₂` `σ`-invariant and `φ : C₂ → C₁` is `σ`-equivariant, its graph
`{(φ y, y) : y ∈ C₂} ⊆ V` is the `σ`-invariant subspace `range (C₁.subtype ∘ φ + C₂.subtype)`.
These graphs are precisely the `σ`-invariant `n`-dimensional subspaces `≠ C₁`, which is the
content of the counting identity.
-/

import Mathlib
import Submission.Work.Higman.Layers.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Higman.Layers

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The graph in `V` of a `σ`-equivariant linear map `φ : C₂ → C₁`, where `C₁, C₂ ≤ V` are
`σ`-invariant. -/
def graphOf {σ : V →ₗ[ZMod 2] V} {C₁ C₂ : Submodule (ZMod 2) V} (h1 : IsInv σ C₁)
    (h2 : IsInv σ C₂) (φ : HomInv σ C₂ C₁ h2 h1) : Submodule (ZMod 2) V :=
  ((C₁.subtype.comp φ.1) + C₂.subtype).range

@[simp]
theorem mem_graphOf {σ : V →ₗ[ZMod 2] V} {C₁ C₂ : Submodule (ZMod 2) V} (h1 : IsInv σ C₁)
    (h2 : IsInv σ C₂) (φ : HomInv σ C₂ C₁ h2 h1) (x : V) :
    x ∈ graphOf h1 h2 φ ↔ ∃ y : C₂, (φ.1 y : V) + (y : V) = x := by
  simp only [graphOf, LinearMap.mem_range, LinearMap.add_apply, LinearMap.comp_apply,
    Submodule.subtype_apply]

end Work.Higman.Layers
