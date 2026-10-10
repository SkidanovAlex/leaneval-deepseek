import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# From vanishing inertia to `ramificationIdx = 1`

The call-site step that turns the inertia statement produced by the compositum lemmas
(`Work.SSGRoute.Sha2Lib.inertia_eq_bot_of_sup`,
`Work.SSGRoute.Sha2Lib.inertia_eq_bot_of_finset_sup`) into the ramification statement that the
rank-one level datum consumes:

    `Ideal.inertia (K ≃ₐ[F] K) q'.asIdeal = ⊥  ⟹  q'.asIdeal.ramificationIdx (𝓞 F) = 1`

(`q'.asIdeal.LiesOver q.asIdeal` supplies the `LiesOver` instance).  This is the `.mp` of
`Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one`, wrapped with
the hypotheses in the exact shape the level bookkeeping has on hand — so that obligation 1 of
`Submission/Work/SSGRoute/NOTE_TPatom_route.md` §3.6 is exactly
`inertia_eq_bot_of_finset_sup` + this lemma + `hgenL`, with nothing else.
-/

open scoped NumberField

namespace Work.SSGRoute.Sha2Lib

/-- **Vanishing inertia gives unramifiedness.**  For a finite Galois extension `K/F` of number
fields and primes `q | q'` of `𝓞 F`, `𝓞 K`: if the inertia subgroup of `Gal(K/F)` at the prime `q'`
is trivial, then `e(q'|q) = 1`. -/
theorem ramificationIdx_eq_one_of_inertia_eq_bot {F K : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [IsGalois F K] [FiniteDimensional F K]
    (q : Ideal (NumberField.RingOfIntegers F)) (q' : Ideal (NumberField.RingOfIntegers K))
    [q.IsPrime] [q'.IsPrime] [q'.LiesOver q]
    (h : Ideal.inertia (K ≃ₐ[F] K) q' = ⊥) :
    q'.ramificationIdx (NumberField.RingOfIntegers F) = 1 :=
  (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one q q').mp h

end Work.SSGRoute.Sha2Lib
