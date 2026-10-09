/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Representation morphisms from equivariant monoid homomorphisms

Let `M`, `N` be commutative groups with `MulDistribMulAction`s of a group `Γ`.  A monoid
homomorphism `f : M →* N` which is `Γ`-equivariant (`f (σ • x) = σ • f x` for all `σ`, `x`)
induces a morphism of `CoeffInt`-linear `Γ`-representations
`Additive M ⟶ Additive N`.

This is the boilerplate that turns each of the subgroup projections of the idèle group used in
`NK.HassePrinciple.hbnIdele` into a morphism of representations.
-/

import Mathlib
import Submission.NK.HassePrinciple.IdelesLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace NK.HassePrinciple

open CategoryTheory Representation

set_option autoImplicit false

noncomputable section

/-- **A morphism of `CoeffInt`-linear representations out of an equivariant monoid
homomorphism.** -/
noncomputable def repHomOfMonoidHom {Γ M N : Type} [Group Γ] [CommGroup M] [CommGroup N]
    [MulDistribMulAction Γ M] [MulDistribMulAction Γ N] (f : M →* N)
    (hf : ∀ (σ : Γ) (x : M), f (σ • x) = σ • f x) :
    Rep.ofDistribMulAction CoeffInt.{0} Γ (Additive M) ⟶
      Rep.ofDistribMulAction CoeffInt.{0} Γ (Additive N) :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul (f (Additive.toMul x))
      map_add' := fun x y => by
        show Additive.ofMul (f (Additive.toMul (x + y))) =
          Additive.ofMul (f (Additive.toMul x)) + Additive.ofMul (f (Additive.toMul y))
        rw [toMul_add, map_mul, ofMul_mul]
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        show Additive.ofMul (f (Additive.toMul (z • x))) =
          z • Additive.ofMul (f (Additive.toMul x))
        rw [toMul_zsmul, map_zpow, ofMul_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (f (σ • Additive.toMul x)) =
          Additive.ofMul (σ • f (Additive.toMul x))
        rw [hf] }

@[simp] theorem repHomOfMonoidHom_apply {Γ M N : Type} [Group Γ] [CommGroup M] [CommGroup N]
    [MulDistribMulAction Γ M] [MulDistribMulAction Γ N] (f : M →* N)
    (hf : ∀ (σ : Γ) (x : M), f (σ • x) = σ • f x) (x : Additive M) :
    (repHomOfMonoidHom f hf).hom x = Additive.ofMul (f (Additive.toMul x)) := rfl

end

end NK.HassePrinciple
