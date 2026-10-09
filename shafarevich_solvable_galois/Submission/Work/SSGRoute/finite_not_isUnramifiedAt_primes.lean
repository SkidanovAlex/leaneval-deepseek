import Mathlib
import Submission.Work.LocalFields.finite_ramified_primes_extension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

namespace Work.SSGRoute

/-- **Only finitely many primes of the top field ramify in a finite Galois extension of number
fields.**

For a finite Galois extension `K/k` of number fields, the set of finite primes `q` of `K` whose
inertia subgroup over `k` is nontrivial (i.e. which are ramified over `k`) is finite.

The proof reduces to the absolute statement for `K`: a prime `q` of `K` that is ramified over
`k` is ramified over `ℤ` — its ramification index over `ℤ` factors as
`e(q/ℤ) = e(v/ℤ) · e(q/k)` for the prime `v` of `k` below `q`, and `e(q/k) ≠ 1` by hypothesis.
The primes of `K` ramified over `ℤ` are exactly the prime divisors of the nonzero different ideal
`differentIdeal ℤ (𝓞 K)`, of which there are finitely many (`Ideal.finite_factors`, via
`dvd_differentIdeal_iff`). -/
theorem finite_not_isUnramifiedAt_primes (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] :
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
      ¬ Work.LocalFields.IsUnramifiedAt k q}.Finite := by
  classical
  -- The primes of `K` ramified over `ℤ` are the prime divisors of the nonzero different ideal,
  -- hence finite.
  have hW : {q : Work.LocalFields.FinitePrime K | ¬ Algebra.IsUnramifiedAt ℤ q.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := differentIdeal ℤ (𝓞 K)) (differentIdeal_ne_bot)).subset ?_
    intro q hq
    exact dvd_differentIdeal_iff.mpr hq
  -- A prime of `K` that is ramified over `k` is ramified over `ℤ`.
  refine hW.subset ?_
  intro q hq
  let v : Work.LocalFields.FinitePrime k :=
    ⟨q.asIdeal.under (𝓞 k), Ideal.IsPrime.under _ _, Ideal.under_ne_bot _ q.ne_bot⟩
  exact Work.LocalFields.not_isUnramifiedAt_int_of_not_isUnramifiedAt v q hq

end Work.SSGRoute
