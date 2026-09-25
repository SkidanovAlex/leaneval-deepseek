import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg

namespace Commons.NumberTheory.NumberField.Completion

theorem natCard_algEquiv_adicCompletion_eq_inertiaDeg_of_ramificationIdx_eq_one {K L : Type*}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  rw [natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq, h1, one_mul]

end Commons.NumberTheory.NumberField.Completion
