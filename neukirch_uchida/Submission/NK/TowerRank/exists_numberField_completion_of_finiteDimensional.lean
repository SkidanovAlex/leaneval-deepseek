import Mathlib
import Submission.NK.Ramification.exists_valuationSubring_finiteDimensional

namespace NK.TowerRank

/-- **Every finite level `M/κ` is a completion of a number field at a prime.**  This is the
"instantiate at each `M`" bridge of the deliverable: it applies
`Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional`
at `B := ↥M` (the target `B` is implicit, so pass it explicitly), letting every per-level local
input — the power class count `NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime` and hence the
arithmetic half of `NK.TowerRank.TowerAbelianRank.abelian_rank`, as well as any per-level
reciprocity datum — be instantiated at number fields and transported back to `M`. -/
theorem exists_numberField_completion_of_finiteDimensional {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    (M : IntermediateField (𝔭.adicCompletion K) K') [FiniteDimensional (𝔭.adicCompletion K) M] :
    ∃ (L : Type*) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hq : q.asIdeal.LiesOver 𝔭.asIdeal),
      letI : Algebra (𝔭.adicCompletion K) (q.adicCompletion L) :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 q hq)
      Nonempty (↥M ≃ₐ[𝔭.adicCompletion K] q.adicCompletion L) := by
  obtain ⟨L, hf, hn, ha, q, hq, hne⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
      (K := K) (Q := 𝔭) (B := ↥M)
  exact ⟨L, hf, hn, ha, q, hq, hne⟩

end NK.TowerRank
