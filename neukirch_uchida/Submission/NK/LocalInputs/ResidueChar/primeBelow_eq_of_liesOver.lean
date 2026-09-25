/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `primeBelow` is determined by the primes lying over it

If a finite prime `𝔮` of a number field `K` lies over the height-one prime `P` of
`𝓞 ℚ = ℤ`, then `P` is the rational prime `𝔮 ∩ ℤ` below `𝔮`, i.e.
`primeBelow K 𝔮 = P`.

Both sides are height-one spectra, so it suffices to compare their underlying ideals:
`(primeBelow K 𝔮).asIdeal = 𝔮.asIdeal.under (𝓞 ℚ)` by definition, and the hypothesis
`𝔮.asIdeal.LiesOver P.asIdeal` says exactly `P.asIdeal = 𝔮.asIdeal.under (𝓞 ℚ)`.
-/
import Mathlib
import Submission.NK.LocalInputs.Defs

namespace NK.LocalInputs.ResidueChar

/-- **The rational prime below `𝔮` is the prime `𝔮` lies over.** -/
theorem primeBelow_eq_of_liesOver {K : Type*} [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : 𝔮.asIdeal.LiesOver P.asIdeal) :
    NK.LocalInputs.primeBelow K 𝔮 = P := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NK.LocalInputs.primeBelow_asIdeal]
  exact h.over.symm

end NK.LocalInputs.ResidueChar
