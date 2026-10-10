import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The residue characteristic of a completion is an automatic prime

The endgame's per-prime hypotheses (see `Submission/Work/Mine/ReducedLocalInputs.lean`) carry the
conjunct `CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p`.  That conjunct is a
*theorem*: the residue field of the ring of integers of a completion at a finite prime is finite
(`Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion`), so its
characteristic `ringChar` is a prime — this file records it, so that the leaf list of the endgame is
not burdened with a trivially true hypothesis.
-/

namespace NK.Mine

open IsDedekindDomain

/-- **The residue field of a completion at a finite prime has prime characteristic.** -/
theorem exists_prime_charP_residueField_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p := by
  haveI : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
  haveI : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
      (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) := inferInstance
  exact ⟨ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)),
    CharP.prime_ringChar _, inferInstance⟩

/-- The residue characteristic itself is a prime, in the form in which the endgame states the
per-prime leaf (no existential over `p`). -/
theorem prime_ringChar_residueField_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))).Prime := by
  haveI : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
  exact CharP.prime_ringChar _

/-- The matching `CharP` instance, exposed as a theorem so that it can be passed explicitly. -/
theorem charP_ringChar_residueField_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
      (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) :=
  inferInstance

end NK.Mine
