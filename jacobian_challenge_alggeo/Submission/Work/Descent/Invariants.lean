/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The invariants of a semilinear Galois action: basic API

Elementary facts about the invariant subalgebra `B^Γ` of a semilinear Galois action on a
`k'`-algebra `B` (see `Submission/Work/Descent/Basic.lean`):

* `Work.Descent.SemilinearAction.actLinearEquiv` — each element of the action as a `k`-linear
  equivalence of `B`;
* `Work.Descent.SemilinearAction.toModule` — the underlying semilinear action on the additive
  group of `B`, so that Speiser's result for modules applies to `B`, and
  `Work.Descent.SemilinearAction.fixed_toModule` identifies the fixed points of that module
  structure with `B^Γ`; this is what makes the algebra case of Speiser a corollary of the module
  case.
* `Work.Descent.SemilinearAction.exists_unique_lift` — the universal property of `B^Γ`: a
  `Γ`-invariant `k`-algebra map out of `B` factors uniquely through `B^Γ`.
-/
import Mathlib
import Submission.Work.Descent.Basic

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

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  {B : Type u} [CommRing B] [Algebra k' B] [Algebra k B] [IsScalarTower k k' B]

namespace SemilinearAction

/-- An element of a semilinear action on a `k'`-algebra, as a `k`-linear equivalence. -/
noncomputable def actLinearEquiv (A : SemilinearAction k k' B) (σ : Gal k k') : B ≃ₗ[k] B where
  toFun := A.act σ
  map_add' := fun b c => map_add (A.act σ) b c
  map_smul' := fun c b => A.act_smul_k σ c b
  invFun := (A.act σ).symm
  left_inv := fun b => by simp
  right_inv := fun b => by simp

@[simp] lemma actLinearEquiv_apply (A : SemilinearAction k k' B) (σ : Gal k k') (b : B) :
    A.actLinearEquiv σ b = A.act σ b := rfl

/-- The semilinear action on the additive group of `B` underlying a semilinear action on the
`k'`-algebra `B`. -/
noncomputable def toModule (A : SemilinearAction k k' B) : SemilinearActionModule k k' B where
  act :=
    { toFun := fun σ => A.actLinearEquiv σ
      map_one' := by ext b; simp [actLinearEquiv, map_one]
      map_mul' := by intro σ τ; ext b; simp [actLinearEquiv, map_mul] }
  act_smul := A.act_smul

/-- The fixed points of the underlying module structure are exactly the invariants. -/
lemma fixed_toModule (A : SemilinearAction k k' B) :
    (A.toModule).fixed = A.invariants.toSubmodule := by
  ext b
  simp only [SemilinearActionModule.mem_fixed, Subalgebra.mem_toSubmodule,
    SemilinearAction.mem_invariants, toModule, MonoidHom.coe_mk, OneHom.coe_mk,
    actLinearEquiv_apply]

end SemilinearAction

variable {C : Type u} [CommSemiring C] [Algebra k C]

/-- The universal property of the invariant subalgebra `B^Γ`: a `Γ`-invariant `k`-algebra map out
of `B` factors uniquely through `B^Γ`. -/
theorem SemilinearAction.exists_unique_lift (A : SemilinearAction k k' B) (f : C →ₐ[k] B)
    (hf : ∀ (σ : Gal k k') (c : C), A.act σ (f c) = f c) :
    ∃! g : C →ₐ[k] A.invariants, A.invariantsSubtype.comp g = f := by
  refine ⟨AlgHom.codRestrict f A.invariants fun c => fun σ => hf σ c, ?_, ?_⟩
  · ext c
    rfl
  · intro g hg
    have hgg : A.invariantsSubtype.comp g =
        A.invariantsSubtype.comp
          (AlgHom.codRestrict f A.invariants fun c => fun σ => hf σ c) := by
      rw [hg]
      ext c
      rfl
    ext c
    simpa using congrArg (fun (φ : C →ₐ[k] B) => φ c) hgg

end Work.Descent
