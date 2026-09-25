/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Two descriptions of the rational prime below a finite prime of `ℚ`

For a finite prime `𝔭` of `ℚ` (i.e. a height-one prime of `𝓞 ℚ ≅ ℤ`) and a natural number `p`, the
two natural descriptions of "`𝔭` is the prime `p`" coincide:

* the residue field of the valuation ring of `ℚ_𝔭` has `p` elements
  (`Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm`), and
* the natural generator of `𝔭` — i.e. `(Rat.HeightOneSpectrum.primesEquiv 𝔭).1` — is `p`.

This bridges the hypothesis used by the commons' `ℚ_p` computations (a cardinality) and the
hypothesis used by `NK.LocalInputs` (a `primesEquiv` value).
-/
import Submission.NK.LocalInputs.Defs
import Submission.NK.LocalInputs.Inputs

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs.ResidueChar

/-- **The residue field cardinality of `ℚ_𝔭` is the rational prime below `𝔭`.** -/
theorem residueCard_eq_primesEquiv (𝔭 : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers ℚ)) (p : ℕ) :
    Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers ℚ)) = p ↔
      (Rat.HeightOneSpectrum.primesEquiv 𝔭).1 = p := by
  rw [Commons.NumberTheory.NumberField.residueCard_adicCompletion_eq_absNorm 𝔭,
    ← Commons.NumberTheory.NumberField.Set.absNorm_eq_primesEquiv 𝔭]

end NK.LocalInputs.ResidueChar
