import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.FrobeniusBridge.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ResidueFrob

open NK.Reconstruct

set_option linter.unusedVariables false

/-- **The prime cut out on a finite level by a place of `K'` is the induced finite place.**

Both `primeOfLevel A L` and `placeOf (primeOf A) A … L` are the (unique) finite place of the level
`L` whose valuation ring is the intersection `A ∩ L` of the place `A` of `K'` with `L`; indeed

* `primeOfLevel_spec` computes the valuation ring of `primeOfLevel A L` as
  `A.comap (algebraMap ↥L K')`, and
* `comap_eq_valuationSubringAtPrime_placeOf` computes the valuation ring of the induced place
  `placeOf (primeOf A) A … L` as the same subring,

so the two primes agree by injectivity of `valuationSubringAtPrime`. -/
theorem primeOfLevel_eq_placeOf {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] :
    NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L) =
      Submission.NeukirchUchida.Local.placeOf (Submission.NeukirchUchida.primeOf A.1 A.2)
        A.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2) L := by
  refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥L) ?_
  rw [← NK.Reconstruct.primeOfLevel_spec A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L),
    ← Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf]

/-- **The prime of a finite level below a place of `K'` lies over the prime of `K` below that
place.**

`primeOfLevel A L` is the finite place of the level `L` whose valuation ring is `A ∩ L`; its trace
on `𝓞 K` is the trace of `A` on `K`, i.e. the prime `primeOf A` of the base field.  Concretely,
`primeOfLevel A L` is the induced place `placeOf (primeOf A) A … L` of `Local.placeOf_liesOver`, so
the claim is the latter's `LiesOver` statement. -/
theorem primeOfLevel_liesOver {K : Type*} [Field K] [NumberField K]
    {K' : Type*} [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] :
    (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)).asIdeal.LiesOver
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal := by
  rw [primeOfLevel_eq_placeOf A L]
  exact Submission.NeukirchUchida.Local.placeOf_liesOver _ A.1 _ L

end NK.ResidueFrob
