import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_inertiaDeg_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one

namespace Commons.NumberTheory.NumberField.Completion

theorem exists_orderOf_eq_inertiaDeg_of_ramificationIdx_eq_one {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      orderOf σ = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : Finite (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := inferInstance
  obtain ⟨σ, hσ⟩ :=
    (isCyclic_iff_exists_orderOf_eq_natCard
      (α := q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)).mp
      (isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one Q q hq h1)
  refine ⟨σ, ?_⟩
  rw [hσ, natCard_algEquiv_adicCompletion_eq_inertiaDeg_of_ramificationIdx_eq_one Q q hq h1]

end Commons.NumberTheory.NumberField.Completion
