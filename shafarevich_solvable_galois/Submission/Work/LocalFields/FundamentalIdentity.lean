/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The fundamental identity of ramification theory

For a finite Galois extension `L/K` of number fields and a finite prime `v` of `K`, the number of
primes above `v` times the order of the decomposition group is `[L : K]`.

## Main results

* `Work.LocalFields.ncard_primesOver_mul_card_decompositionGroup_eq_finrank`.
-/
import Submission.Work.LocalFields.Decomposition
import Submission.Work.LocalFields.card_decompositionGroup_mul_ncard
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Pointwise Valued WithZero

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The fundamental identity.**  For a finite Galois extension of number fields, the number of
primes above `v` times the order of any decomposition group above `v` is the degree `[L : K]`. -/
theorem ncard_primesOver_mul_card_decompositionGroup_eq_finrank (v : FinitePrime K)
    (w : FinitePrime L) [hw : w.asIdeal.LiesOver v.asIdeal] :
    (v.asIdeal.primesOver (𝓞 L)).ncard * Nat.card (decompositionGroup K w) =
      Module.finrank K L := by
  rw [mul_comm, card_decompositionGroup_mul_ncard, IsGalois.card_aut_eq_finrank]

/-- The order of the Galois group is the degree of the extension. -/
theorem card_galoisGroup_eq_finrank : Nat.card Gal(L/K) = Module.finrank K L :=
  IsGalois.card_aut_eq_finrank K L

end Work.LocalFields
