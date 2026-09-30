/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Speiser's comparison maps as equivalences

The bijectivity statements of Speiser's descent result (`Work.Descent.moduleSpeiser`,
`Work.Descent.speiser`) repackaged as linear resp. ring and algebra equivalences, for use by the
descent of the group structure in the geometric half of area DS:

* `Work.Descent.SemilinearActionModule.speiserEquiv : V^Γ ⊗_k k' ≃ₗ[k] V`;
* `Work.Descent.SemilinearAction.speiserLinearEquiv : B^Γ ⊗_k k' ≃ₗ[k] B`;
* `Work.Descent.SemilinearAction.speiserAlgEquiv : B^Γ ⊗_k k' ≃ₐ[k] B`;
* `Work.Descent.SemilinearAction.speiserRingEquiv : B^Γ ⊗_k k' ≃+* B`.
-/
import Mathlib
import Submission.Work.Descent.Basic
import Submission.Work.Descent.moduleSpeiser
import Submission.Work.Descent.speiser
import Submission.Work.Descent.Invariants

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

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [IsGalois k k']

namespace SemilinearActionModule

variable {V : Type u} [AddCommGroup V] [Module k' V] [Module k V] [IsScalarTower k k' V]

/-- Speiser's comparison map for a semilinear action on a `k'`-module, as a `k`-linear
equivalence. -/
noncomputable def speiserEquiv (A : SemilinearActionModule k k' V) : A.fixed ⊗[k] k' ≃ₗ[k] V :=
  LinearEquiv.ofBijective A.speiserMapK (moduleSpeiser A)

@[simp] lemma speiserEquiv_tmul (A : SemilinearActionModule k k' V) (v : A.fixed) (c : k') :
    A.speiserEquiv (v ⊗ₜ[k] c) = c • (v : V) := rfl

end SemilinearActionModule

namespace SemilinearAction

variable {B : Type u} [CommRing B] [Algebra k' B] [Algebra k B] [IsScalarTower k k' B]

/-- Speiser's comparison map for a semilinear action on a `k'`-algebra, as a `k`-linear
equivalence. -/
noncomputable def speiserLinearEquiv (A : SemilinearAction k k' B) :
    A.invariants ⊗[k] k' ≃ₗ[k] B :=
  LinearEquiv.ofBijective (A.speiserHomK : A.invariants ⊗[k] k' →ₗ[k] B) (speiser A)

/-- Speiser's comparison map for a semilinear action on a `k'`-algebra, as a `k`-algebra
equivalence. -/
noncomputable def speiserAlgEquiv (A : SemilinearAction k k' B) :
    A.invariants ⊗[k] k' ≃ₐ[k] B :=
  AlgEquiv.ofBijective A.speiserHomK (speiser A)

/-- Speiser's comparison map for a semilinear action on a `k'`-algebra, as a ring equivalence. -/
noncomputable def speiserRingEquiv (A : SemilinearAction k k' B) :
    A.invariants ⊗[k] k' ≃+* B :=
  (A.speiserAlgEquiv : A.invariants ⊗[k] k' ≃+* B)

@[simp] lemma speiserAlgEquiv_apply (A : SemilinearAction k k' B)
    (x : A.invariants ⊗[k] k') : A.speiserAlgEquiv x = A.speiserHomK x :=
  AlgEquiv.ofBijective_apply A.speiserHomK (speiser A) x

@[simp] lemma speiserAlgEquiv_tmul (A : SemilinearAction k k' B) (b : A.invariants) (c : k') :
    A.speiserAlgEquiv (b ⊗ₜ[k] c) = c • (b : B) := by
  rw [speiserAlgEquiv_apply, SemilinearAction.speiserHomK_tmul]

/-- Speiser's comparison map is `k'`-linear, recorded on pure tensors (the `k'`-algebra structure
on `B^Γ ⊗_k k'` given by the second tensor factor is not a global Mathlib instance, see the
implementation notes of `Submission/Work/Descent/Basic.lean`): `c • (b ⊗ c') = b ⊗ (c * c')`. -/
@[simp] lemma speiserAlgEquiv_smul_tmul (A : SemilinearAction k k' B) (c c' : k')
    (b : A.invariants) :
    A.speiserAlgEquiv (b ⊗ₜ[k] (c * c')) = c • A.speiserAlgEquiv (b ⊗ₜ[k] c') := by
  rw [speiserAlgEquiv_apply, speiserAlgEquiv_apply,
    SemilinearAction.speiserHomK_smul_tmul]

@[simp] lemma speiserRingEquiv_smul_tmul (A : SemilinearAction k k' B) (c c' : k')
    (b : A.invariants) :
    A.speiserRingEquiv (b ⊗ₜ[k] (c * c')) = c • A.speiserRingEquiv (b ⊗ₜ[k] c') := by
  have h := speiserAlgEquiv_smul_tmul A c c' b
  simpa [speiserRingEquiv] using h

@[simp] lemma speiserRingEquiv_tmul (A : SemilinearAction k k' B) (b : A.invariants) (c : k') :
    A.speiserRingEquiv (b ⊗ₜ[k] c) = c • (b : B) := by
  have h := speiserAlgEquiv_tmul A b c
  simpa [speiserRingEquiv] using h

end SemilinearAction

end Work.Descent
