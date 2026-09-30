/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Descent of Galois-invariant morphisms

The corollary of `Work.Descent.baseChange_isQuotient` which is the form used for the descent of the
group structure of the Jacobian: a `k`-morphism `X ×_k Spec k' ⟶ Y` which is invariant under the
action of `Gal k k'` (on the source) descends uniquely to a `k`-morphism `X ⟶ Y`.
-/
import Mathlib
import Submission.Work.Descent.Scheme
import Submission.Work.Descent.baseChange_isQuotient

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

/-- Descent of a `Γ`-invariant morphism of `k`-schemes from `X ×_k Spec k'` to `X`: this is the
instance of `Work.Descent.IsGaloisQuotient` provided by `Work.Descent.baseChange_isQuotient`. -/
theorem desc_of_invariant {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (X Y : Sch k)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (Φ : (baseChange (k := k) (k' := k') X).left ⟶ Y.left)
    (hΦ : Φ ≫ Y.hom = (baseChange (k := k) (k' := k') X).hom ≫ specMap k k')
    (h : ∀ σ : Gal k k', galAct (k := k) (k' := k') X σ ≫ Φ = Φ) :
    ∃! φ : X ⟶ Y, baseChangeπ (k := k) (k' := k') X ≫ φ.left = Φ :=
  baseChange_isQuotient X Y Φ hΦ h

end Work.Descent
