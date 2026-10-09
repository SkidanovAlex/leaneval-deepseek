/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The compositum of Kummer fields attached to a family of local `ℓ`-power classes

For a number field `L` with a prime `ℓ`, a finite set `T` of finite primes of `L`, a family
`b : PrimeIdeal L → Lˣ` of units and a fixed ambient field `K' ⊇ L`, `kummerSup ℓ T b` is the
compositum, over the primes `P ∈ T`, of the Kummer fields `L(b_P^{1/ℓ}) ⊆ K'`.

This is the field produced by the Kummer-theoretic embedding problem of §6 of
arXiv:2601.01251 (Uchida's method): each `b_P` realises a prescribed tuple of local `ℓ`-power
classes at the primes of `T`, and the compositum is the abelian extension of exponent `ℓ` in
which the prescribed primes split.
-/
import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.LocalAnabelian.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer.Embedding

open scoped Classical

/-- The compositum, over the primes of `T`, of the Kummer fields `L(b_P^{1/ℓ})` inside `K'`. -/
noncomputable def kummerSup {L K' : Type*} [Field L] [NumberField L] [Field K'] [Algebra L K']
    (ℓ : ℕ) (T : Finset (NK.Chebotarev.PrimeIdeal L)) (b : NK.Chebotarev.PrimeIdeal L → Lˣ) :
    IntermediateField L K' :=
  T.sup (fun P => NK.LocalAnabelian.kummerField (K' := K') ℓ (b P))

end NK.UchidaKummer.Embedding
