/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# From the local degrees to the global degree

This file contains the last bookkeeping step which turns the *local* input of
Neukirch–Uchida — the preservation of `[K_𝔭 : ℚ_p]` for corresponding places — into the equality
of the global degrees `[K₁ : ℚ] = [K₂ : ℚ]`, which is what the Čebotarev reconstruction consumes.

Given a prime `p` of `ℚ`, a bijection `e` between the primes of `K₁` above `p` and the primes of
`K₂` above `p`, and the pointwise equality of the local degrees along `e`, the global degrees are
equal.  The proof is the additivity of the local degrees
(`NK.LocalInputs.Degree.sum_localDegree_eq_finrank`) plus the reindexing of the sum along `e`.

The bijection `e` in the application is the one produced by the local correspondence
(`Submission.NeukirchUchida/PrimeCorrespondence.lean`, `primeMap`), and the pointwise equality of
the local degrees is
`NK.LocalInputs.residueChar_and_localDegree_eq_of_decompositionGroup`.
-/
import Submission.NK.LocalInputs.Degree.sum_localDegree_eq_finrank

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.LocalInputs

/-- **The global degree is the sum of the local degrees, transported along a bijection of the
primes above a fixed rational prime.** -/
theorem finrank_eq_of_localDegree_eq {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (e : P.asIdeal.primesOver (NumberField.RingOfIntegers K₁) ≃
      P.asIdeal.primesOver (NumberField.RingOfIntegers K₂))
    (h : ∀ qq : P.asIdeal.primesOver (NumberField.RingOfIntegers K₁),
      localDegree K₁
          (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ (K := ℚ) (L := K₁) P qq) =
        localDegree K₂
          (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ (K := ℚ) (L := K₂) P
            (e qq))) :
    Module.finrank ℚ K₁ = Module.finrank ℚ K₂ := by
  rw [← Degree.sum_localDegree_eq_finrank K₁ P, ← Degree.sum_localDegree_eq_finrank K₂ P]
  rw [← Equiv.sum_comp e
    (fun qq => localDegree K₂
      (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ (K := ℚ) (L := K₂) P qq))]
  exact Finset.sum_congr rfl fun qq _ => h qq

end NK.LocalInputs
