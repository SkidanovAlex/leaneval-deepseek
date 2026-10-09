import Mathlib
import Submission.NK.Ramification.CommonsBridge
import Submission.NK.Ramification.ramificationSubgroup_map_conj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.Ramification

universe uK uB

/-- A finite-dimensional extension of a `p`-adic field is the `q`-adic completion of a number
field, in a prescribed universe. -/
private theorem exists_adicCompletion_iso {K : Type uK} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B : Type uB} [Field B] [Algebra (Q.adicCompletion K) B]
    [FiniteDimensional (Q.adicCompletion K) B] :
    ∃ (L : Type uB) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hq : q.asIdeal.LiesOver Q.asIdeal),
      letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
      Nonempty (B ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
  Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional_aux.{uK, uB, uB} Q

theorem exists_valuationSubring_finiteDimensional {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B : Type*} [Field B] [Algebra (Q.adicCompletion K) B]
    [FiniteDimensional (Q.adicCompletion K) B] :
    ∃ A : ValuationSubring B,
      IsDiscreteValuationRing A ∧ A.decompositionSubgroup (Q.adicCompletion K) = ⊤ := by
  obtain ⟨L, hLf, hLn, hALK, q, hq, hne⟩ := exists_adicCompletion_iso (K := K) (B := B) Q
  letI := hLf
  letI := hLn
  letI := hALK
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  obtain ⟨e⟩ := hne
  let A₂ : ValuationSubring (q.adicCompletion L) := q.adicCompletionIntegers L
  let A : ValuationSubring B := A₂.comap e.toAlgHom.toRingHom
  have hA : ∀ x : B, x ∈ A ↔ e x ∈ A₂ := fun x => ValuationSubring.mem_comap
  have hA₂ : A₂.decompositionSubgroup (Q.adicCompletion K) = ⊤ :=
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_adicCompletionIntegers_eq_top Q q hq
  refine ⟨A, ?_, ?_⟩
  · exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (A := A₂) (B := A) (ringEquivOfMap A A₂ e hA).symm
  · rw [Subgroup.eq_top_iff']
    intro σ
    exact (conjugationMulEquiv_mem_decompositionSubgroup_iff A A₂ e hA σ).mp
      (by rw [hA₂]; exact Subgroup.mem_top _)

end NK.Ramification
