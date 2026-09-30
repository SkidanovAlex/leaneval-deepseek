/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Galois descent along a Galois extension (area DS): the basic language

This file sets up the language of *semilinear* actions of the Galois group `Γ = Gal(k'/k)` of a
field extension `k'/k` on `k'`-modules and `k'`-algebras:

* `Work.Descent.Gal k k'` -- the Galois group `k' ≃ₐ[k] k'`;
* `Work.Descent.SemilinearActionModule` -- a `k`-linear action of `Γ` on a `k'`-module whose
  elements are `σ`-semilinear;
* `Work.Descent.SemilinearAction` -- the same for a `k'`-algebra, acting by ring automorphisms;
* `Work.Descent.SemilinearActionModule.fixed`,
  `Work.Descent.SemilinearAction.invariants` -- the fixed points, as a `k`-submodule resp. a
  `k`-subalgebra;
* `Work.Descent.SemilinearActionModule.speiserMapK`,
  `Work.Descent.SemilinearAction.speiserHomK` -- the canonical comparison maps `V^Γ ⊗_k k' → V`
  resp. `B^Γ ⊗_k k' → B`, `v ⊗ c ↦ c • v`, whose bijectivity is Speiser's lemma (proved in
  `Submission/Work/Descent/Speiser.lean`);
* `Work.Descent.baseChangeAct` -- the action of `Γ` on `A ⊗_k k'` for a `k`-algebra `A` (acting on
  the second tensor factor); this is the algebraic incarnation of the action of `Γ` on
  `X ×_k Spec k'` by `id_X × Spec σ`.

Everything here is pure algebra; no scheme theory is involved.

## Implementation notes

* As in the rest of Mathlib we do *not* ask the typeclass system to manufacture the `k`-structure
  of a `k'`-module, so the structures below carry the `k`-module (resp. `k`-algebra) structure and
  the compatibility `IsScalarTower` as explicit typeclass arguments.
* Mathlib does not install the `k'`-algebra structure on `A ⊗_k k'` acting on the *second* factor
  (`Algebra.TensorProduct.rightAlgebra`) as a global instance, because it would be ambiguous when
  `A` is itself a `k'`-algebra.  We therefore state the comparison maps of Speiser's lemma as `k`-linear
  resp. `k`-algebra maps (`speiserMapK`, `speiserHomK`) -- which loses nothing, since bijectivity is
  a statement about the underlying function -- and record their `k'`-semilinearity separately
  (`speiserMapK_smul_tmul`, `speiserHomK_smul_tmul`).  Similarly the action of `Γ` on `A ⊗_k k'` is
  a group homomorphism into the *ring* automorphisms of `A ⊗_k k'`, see `baseChangeAct`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct

universe u

namespace Work.Descent

/-! ## The Galois group -/

/-- The Galois group of the extension `k'/k`: the group of `k`-algebra automorphisms of `k'`.  For
`k'/k` finite Galois this is the usual Galois group. -/
abbrev Gal (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : Type u := k' ≃ₐ[k] k'

/-! ## Semilinear actions on modules -/

/-- A `k`-semilinear action of the Galois group `Gal k k'` on a `k'`-module `V` (which is also
equipped with a compatible `k`-module structure): each `σ` acts by a `k`-linear automorphism of
`V`, `σ`-semilinearly. -/
structure SemilinearActionModule (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (V : Type u) [AddCommGroup V] [Module k' V] [Module k V] [IsScalarTower k k' V] where
  /-- The action. -/
  act : Gal k k' →* V ≃ₗ[k] V
  /-- Semilinearity of the action. -/
  act_smul : ∀ (σ : Gal k k') (c : k') (v : V), act σ (c • v) = σ c • act σ v

namespace SemilinearActionModule

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  {V : Type u} [AddCommGroup V] [Module k' V] [Module k V] [IsScalarTower k k' V]
  (A : SemilinearActionModule k k' V)

@[simp] lemma act_one : A.act 1 = 1 := map_one A.act

@[simp] lemma act_mul (σ τ : Gal k k') : A.act (σ * τ) = A.act σ * A.act τ := map_mul A.act σ τ

/-- The fixed points of a semilinear action, as a `k`-submodule. -/
def fixed : Submodule k V where
  carrier := {v | ∀ σ : Gal k k', A.act σ v = v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy σ
    rw [map_add, hx σ, hy σ]
  smul_mem' := by
    intro c x hx σ
    rw [map_smul, hx σ]

variable {A}

@[simp] lemma mem_fixed {v : V} : v ∈ A.fixed ↔ ∀ σ : Gal k k', A.act σ v = v := Iff.rfl

lemma act_eq_of_mem_fixed {v : V} (hv : v ∈ A.fixed) (σ : Gal k k') : A.act σ v = v := hv σ

/-- The inclusion `V^Γ ↪ V`. -/
def fixedSubtype : A.fixed →ₗ[k] V := A.fixed.subtype

@[simp] lemma fixedSubtype_apply (v : A.fixed) : A.fixedSubtype v = (v : V) := rfl

/-- The comparison map `V^Γ ⊗_k k' → V`, `v ⊗ c ↦ c • v`. -/
noncomputable def speiserMapK (A : SemilinearActionModule k k' V) :
    A.fixed ⊗[k] k' →ₗ[k] V :=
  TensorProduct.lift
    (LinearMap.mk₂ k (fun v c => c • (v : V))
      (by intro v w c; simp)
      (by intro a v c; exact (smul_comm a c (v : V)).symm)
      (by intro v c d; simp [add_smul])
      (by intro a v c; simp [smul_assoc]))

@[simp] lemma speiserMapK_tmul (A : SemilinearActionModule k k' V) (v : A.fixed) (c : k') :
    A.speiserMapK (v ⊗ₜ[k] c) = c • (v : V) := rfl

@[simp] lemma speiserMapK_tmul_one (A : SemilinearActionModule k k' V) (v : A.fixed) :
    A.speiserMapK (v ⊗ₜ[k] (1 : k')) = (v : V) := by simp

/-- The comparison map `V^Γ ⊗_k k' → V` is `k'`-linear on pure tensors: this is the computation
`c • (v ⊗ c') = v ⊗ (c * c')`. -/
@[simp] lemma speiserMapK_smul_tmul (A : SemilinearActionModule k k' V) (c c' : k') (v : A.fixed) :
    A.speiserMapK (v ⊗ₜ[k] (c * c')) = c • A.speiserMapK (v ⊗ₜ[k] c') := by
  rw [speiserMapK_tmul, speiserMapK_tmul, smul_smul, mul_comm]

end SemilinearActionModule

/-! ## Semilinear actions on algebras -/

/-- A `k`-semilinear action of the Galois group `Gal k k'` on a `k'`-algebra `B` (which is also
equipped with a compatible `k`-algebra structure): each `σ` acts by a ring automorphism of `B`,
`σ`-semilinearly. -/
structure SemilinearAction (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (B : Type u)
    [CommSemiring B] [Algebra k' B] [Algebra k B] [IsScalarTower k k' B] where
  /-- The action. -/
  act : Gal k k' →* B ≃+* B
  /-- Semilinearity of the action. -/
  act_smul : ∀ (σ : Gal k k') (c : k') (b : B), act σ (c • b) = σ c • act σ b

namespace SemilinearAction

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  {B : Type u} [CommSemiring B] [Algebra k' B] [Algebra k B] [IsScalarTower k k' B]
  (A : SemilinearAction k k' B)

@[simp] lemma act_one : A.act 1 = 1 := map_one A.act

@[simp] lemma act_mul (σ τ : Gal k k') : A.act (σ * τ) = A.act σ * A.act τ := map_mul A.act σ τ

/-- Semilinearity, evaluated on `algebraMap`. -/
@[simp] lemma act_algebraMap (σ : Gal k k') (c : k') :
    A.act σ (algebraMap k' B c) = algebraMap k' B (σ c) := by
  simpa [Algebra.smul_def] using A.act_smul σ c 1

/-- The action is `k`-linear. -/
lemma act_smul_k (σ : Gal k k') (c : k) (b : B) : A.act σ (c • b) = c • A.act σ b := by
  rw [Algebra.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply k k' B c,
    map_mul, act_algebraMap, σ.commutes c]

/-- The invariant subalgebra `B^Γ`, as a `k`-subalgebra of `B`. -/
def invariants : Subalgebra k B where
  carrier := {b | ∀ σ : Gal k k', A.act σ b = b}
  mul_mem' := by
    intro x y hx hy σ
    rw [map_mul, hx σ, hy σ]
  one_mem' := by
    intro σ
    rw [map_one]
  add_mem' := by
    intro x y hx hy σ
    rw [map_add, hx σ, hy σ]
  zero_mem' := by
    intro σ
    rw [map_zero]
  algebraMap_mem' := by
    intro c σ
    rw [Algebra.algebraMap_eq_smul_one, A.act_smul_k, map_one]

variable {A}

@[simp] lemma mem_invariants {b : B} : b ∈ A.invariants ↔ ∀ σ : Gal k k', A.act σ b = b :=
  Iff.rfl

lemma act_eq_of_mem_invariants {b : B} (hb : b ∈ A.invariants) (σ : Gal k k') :
    A.act σ b = b := hb σ

/-- The inclusion `B^Γ ↪ B`. -/
def invariantsSubtype : A.invariants →ₐ[k] B := A.invariants.val

@[simp] lemma invariantsSubtype_apply (b : A.invariants) : A.invariantsSubtype b = (b : B) := rfl

/-- The Speiser comparison map `B^Γ ⊗_k k' → B`, `b ⊗ c ↦ c • b`. -/
noncomputable def speiserHomK (A : SemilinearAction k k' B) : A.invariants ⊗[k] k' →ₐ[k] B :=
  Algebra.TensorProduct.lift A.invariantsSubtype (IsScalarTower.toAlgHom k k' B)
    (fun _ _ => Commute.all _ _)

@[simp] lemma speiserHomK_tmul (A : SemilinearAction k k' B) (b : A.invariants) (c : k') :
    A.speiserHomK (b ⊗ₜ[k] c) = c • (b : B) := by
  rw [speiserHomK, Algebra.TensorProduct.lift_tmul, IsScalarTower.toAlgHom_apply,
    Algebra.smul_def, invariantsSubtype_apply, mul_comm]

@[simp] lemma speiserHomK_tmul_one (A : SemilinearAction k k' B) (b : A.invariants) :
    A.speiserHomK (b ⊗ₜ[k] (1 : k')) = (b : B) := by
  rw [speiserHomK_tmul, one_smul]

/-- The Speiser comparison map is `k'`-linear on pure tensors: this is the computation
`c • (b ⊗ c') = b ⊗ (c * c')`. -/
@[simp] lemma speiserHomK_smul_tmul (A : SemilinearAction k k' B) (c c' : k') (b : A.invariants) :
    A.speiserHomK (b ⊗ₜ[k] (c * c')) = c • A.speiserHomK (b ⊗ₜ[k] c') := by
  rw [speiserHomK_tmul, speiserHomK_tmul, smul_smul, mul_comm]

end SemilinearAction

/-! ## The action of `Γ` on `A ⊗_k k'` -/

section BaseChangeAct

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] (A : Type u) [CommRing A]
  [Algebra k A]

/-- The action of `Γ = Gal k k'` on `A ⊗_k k'` by `k`-algebra automorphisms acting on the second
tensor factor.  This is the algebraic incarnation of the action of `Γ` on `X ×_k Spec k'` by
`id_X × Spec σ`. -/
noncomputable def baseChangeAlgEquiv (σ : Gal k k') : (A ⊗[k] k') ≃ₐ[k] (A ⊗[k] k') :=
  Algebra.TensorProduct.congr (AlgEquiv.refl (R := k)) σ

@[simp] lemma baseChangeAlgEquiv_tmul (σ : Gal k k') (a : A) (c : k') :
    baseChangeAlgEquiv A σ (a ⊗ₜ[k] c) = a ⊗ₜ[k] (σ c) := by
  simp [baseChangeAlgEquiv, Algebra.TensorProduct.congr_apply]

@[simp] lemma baseChangeAlgEquiv_one :
    baseChangeAlgEquiv A (1 : Gal k k') = AlgEquiv.refl := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul a c => simp
  | add x y hx hy => simp [hx, hy]

@[simp] lemma baseChangeAlgEquiv_trans (σ τ : Gal k k') :
    baseChangeAlgEquiv A (σ.trans τ) =
      (baseChangeAlgEquiv A σ).trans (baseChangeAlgEquiv A τ) := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul a c => simp [AlgEquiv.trans_apply]
  | add x y hx hy => simp [hx, hy]

/-- Semilinearity of the base change action, stated with `includeRight` so that no `k'`-algebra
structure on `A ⊗_k k'` is needed. -/
lemma baseChangeAlgEquiv_mul_includeRight (σ : Gal k k') (c : k') (x : A ⊗[k] k') :
    baseChangeAlgEquiv A σ ((1 : A) ⊗ₜ[k] c * x) =
      (1 : A) ⊗ₜ[k] (σ c) * baseChangeAlgEquiv A σ x := by
  rw [map_mul, baseChangeAlgEquiv_tmul]

end BaseChangeAct

end Work.Descent
