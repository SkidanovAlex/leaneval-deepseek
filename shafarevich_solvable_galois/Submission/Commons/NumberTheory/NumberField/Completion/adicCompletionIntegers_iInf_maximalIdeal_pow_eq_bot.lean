import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.RegularLocalRing.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

/-- The intersection of all powers of the maximal ideal of the ring of integers of the
`v`-adic completion of a number field is trivial.

This is the Krull intersection theorem applied to the local ring `v.adicCompletionIntegers K`:
this ring is a discrete valuation ring, hence Noetherian and local, so for the (proper) maximal
ideal `m` the theorem `Ideal.iInf_pow_eq_bot_of_isLocalRing` gives `⨅ n, m ^ n = ⊥`. -/
theorem adicCompletionIntegers_iInf_maximalIdeal_pow_eq_bot (K : Type*) [Field K]
    [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (⨅ n : ℕ, IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) = ⊥ := by
  exact Ideal.iInf_pow_eq_bot_of_isLocalRing _
    (IsLocalRing.maximalIdeal.isMaximal (v.adicCompletionIntegers K)).ne_top

end Commons.NumberTheory.NumberField.Completion