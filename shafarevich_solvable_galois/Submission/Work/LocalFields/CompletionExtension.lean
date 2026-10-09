/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The local extension `K_v → L_w`

If `w` is a finite prime of `L` lying over the finite prime `v` of `K`, then the completion
`L_w` is a `K_v`-algebra: the map `K → L → L_w` is uniformly continuous for the `v`-adic
topology, so it extends to the completion.  The canonical map, the induced `Algebra` structure
(together with `IsScalarTower K K_v L_w` and `ContinuousSMul K_v L_w`) and the fact that `L_w` is
a finite `K_v`-module are all constructed in
`Work.LocalFields.nonempty_galois_completion_equiv` (namespace `Work.LocalFields.CompletionHom`).

This file only fixes the *names* used downstream.

## Main definitions

* `Work.LocalFields.completionMap` : the structural map `K_v →+* L_w`.
* `Work.LocalFields.localGaloisGroup` : the local Galois group `Gal(L_w/K_v)`.

## Main results

* `Work.LocalFields.nonempty_localGaloisGroup_mulEquiv_decompositionGroup` :
  `Gal(L_w/K_v) ≃* D_w`.
-/
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.nonempty_galois_completion_equiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The canonical ring homomorphism `K_v →+* L_w` of the local extension at `w | v`. -/
noncomputable abbrev completionMap (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] : Completion K v →+* Completion L w :=
  CompletionHom.ringHom v w

/-- The **local Galois group** `Gal(L_w/K_v)` of the local extension at `w | v`. -/
noncomputable abbrev localGaloisGroup (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] : Type _ :=
  (Completion L w) ≃ₐ[Completion K v] (Completion L w)

/-- **The local Galois group is the decomposition group.**  For a finite Galois extension `L/K`
of number fields and a prime `w` of `L` over `v`, the Galois group of the local extension
`L_w/K_v` is canonically the decomposition group `D_w`. -/
theorem nonempty_localGaloisGroup_mulEquiv_decompositionGroup (v : FinitePrime K)
    (w : FinitePrime L) [hw : w.asIdeal.LiesOver v.asIdeal] :
    Nonempty (localGaloisGroup v w ≃* decompositionGroup K w) :=
  nonempty_galois_completion_equiv v w

end Work.LocalFields
