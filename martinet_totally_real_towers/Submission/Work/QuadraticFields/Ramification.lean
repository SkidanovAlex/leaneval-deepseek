import Mathlib
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.RamificationInertia.inertia_map_restrictNormalHom_le
import Submission.Commons.FieldTheory.Galois.fixingSubgroup_iSup_of_fintype

/-!
# Unramified extensions via inertia groups

This file contains the ramification-theoretic engine of the quadratic-field chapter: a criterion
that reduces the unramifiedness of an extension `M/F` (both subfields of a common Galois extension
`M/ℚ`) to the triviality of an inertia group, plus the bookkeeping that turns facts about the
quadratic subfields of `M` into inertia-group statements.

## Main definitions

* `Work.QuadraticFields.IsUnramifiedAtFinitePrimes F M`: every prime of `𝓞 M` above a prime of
  `𝓞 F` has ramification index `1`.

## Main results

* `ramificationIdx_eq_one_of_inertia_le_fixingSubgroup`: if the inertia group of `𝔓` in `Gal(M/ℚ)`
  is contained in the fixing subgroup of an intermediate field `K` with `F ⊔ K = ⊤`, then `𝔓` is
  unramified over `𝓞 ↥F`.
* `inertia_le_fixingSubgroup_of_unramified`: if `ℚ ⊆ L ⊆ M` and `p` is unramified in `L/ℚ`, then
  the inertia group of a prime above `p` is contained in the fixing subgroup of `L`.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

open NumberField

noncomputable section

/-- A finite extension of number fields `M/F` is unramified at all finite primes if every prime
`𝔓` of `𝓞 M` lying over a prime `𝔭 ≠ ⊥` of `𝓞 F` has ramification index one. -/
def IsUnramifiedAtFinitePrimes (F : Type*) [Field F] [NumberField F] (M : Type*) [Field M]
    [NumberField M] [Algebra F M] : Prop :=
  ∀ (𝔭 : Ideal (𝓞 F)) (𝔓 : Ideal (𝓞 M)), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
    𝔓 ∈ 𝔭.primesOver (𝓞 M) → 𝔓.ramificationIdx (𝓞 F) = 1

end

end Work.QuadraticFields
