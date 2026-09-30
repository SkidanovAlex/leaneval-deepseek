/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Set-up for the Galois quotient of a base change

This file collects the definitions used by `Work.Descent.baseChange_isQuotient`:

* `Work.Descent.Aff k A` -- the affine model `Spec A` as a `k`-scheme;
* `Work.Descent.galoisLeft`, `Work.Descent.galoisRight`, `Work.Descent.galoisLeftA` -- the two
  algebra maps whose tensor product splits `A ⊗_k (k' ⊗_k k')` as `∏_σ (A ⊗_k k')`.

Everything here is a definition; the theorems live in the separate files that import this one.
-/
import Mathlib
import Submission.Work.Descent.Basic
import Submission.Work.Descent.Scheme

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Work.Descent

/-- The affine model over `k` of a `k`-algebra `A`: `Spec A` as a `k`-scheme. -/
noncomputable def Aff (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A] : Sch k :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

/-- The `k`-algebra map `k' → ∏_σ k'` sending `x` to the family `σ ↦ σ x`. -/
noncomputable def galoisLeft (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    k' →ₐ[k] (Gal k k' → k') where
  toFun x σ := σ x
  map_one' := by ext σ; simp
  map_mul' x y := by ext σ; simp
  map_zero' := by ext σ; simp
  map_add' x y := by ext σ; simp
  commutes' c := by
    ext σ
    simp

/-- The `k`-algebra map `k' → ∏_σ k'` sending `y` to the constant family. -/
noncomputable def galoisRight (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    k' →ₐ[k] (Gal k k' → k') where
  toFun y _ := y
  map_one' := by ext σ; simp
  map_mul' x y := by ext σ; simp
  map_zero' := by ext σ; simp
  map_add' x y := by ext σ; simp
  commutes' c := by
    ext σ
    simp

/-- The `A`-algebra map `B → ∏_σ B`, `x ↦ (σ ↦ (id_A ⊗ σ) x)`, where `B = A ⊗_k k'`. -/
noncomputable def galoisLeftA (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (A : Type u) [CommRing A] [Algebra k A] :
    (A ⊗[k] k') →ₐ[A] (Gal k k' → (A ⊗[k] k')) where
  toFun x σ := baseChangeAlgEquiv A σ x
  map_one' := by ext σ; simp
  map_mul' x y := by ext σ; simp
  map_zero' := by ext σ; simp
  map_add' x y := by ext σ; simp
  commutes' a := by ext σ; simp

/-- The `A`-algebra map `B → ∏_σ B` sending `y` to the constant family, where `B = A ⊗_k k'`. -/
noncomputable def galoisRightA (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (A : Type u) [CommRing A] [Algebra k A] :
    (A ⊗[k] k') →ₐ[A] (Gal k k' → (A ⊗[k] k')) where
  toFun y _ := y
  map_one' := by ext σ; simp
  map_mul' x y := by ext σ; simp
  map_zero' := by ext σ; simp
  map_add' x y := by ext σ; simp
  commutes' a := by ext σ; simp

end Work.Descent
