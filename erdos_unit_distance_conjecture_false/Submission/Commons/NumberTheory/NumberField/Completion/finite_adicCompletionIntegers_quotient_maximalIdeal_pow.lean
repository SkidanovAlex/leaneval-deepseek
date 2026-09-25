import Mathlib
import Submission.Commons.NumberTheory.NumberField.adicCompletionIntegers_quotient_equiv

open IsDedekindDomain

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField.Completion

/-- The ring of integers of the `v`-adic completion of a number field, reduced modulo a power of
its maximal ideal, is finite.

Indeed, the natural map `𝓞 K ⧸ v ^ n → (v.adicCompletionIntegers K) ⧸ 𝔪 ^ n` is a ring isomorphism
(`Commons.NumberTheory.NumberField.adicCompletionIntegers_quotient_equiv`), and `𝓞 K ⧸ v ^ n` is
finite because `𝓞 K` is a domain which is a finite `ℤ`-module, hence has finite quotients. -/
theorem finite_adicCompletionIntegers_quotient_maximalIdeal_pow (K : Type*) [Field K]
    [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (n : ℕ) :
    Finite (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) := by
  obtain ⟨e, -⟩ :=
    Commons.NumberTheory.NumberField.adicCompletionIntegers_quotient_equiv (K := K) v n
  haveI hfin : Finite (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ n) := by
    haveI : Finite (NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
      Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    exact Ideal.finite_quotient_pow (Ideal.fg_of_isNoetherianRing v.asIdeal) n
  exact Finite.of_equiv _ e.toEquiv

end Commons.NumberTheory.NumberField.Completion
