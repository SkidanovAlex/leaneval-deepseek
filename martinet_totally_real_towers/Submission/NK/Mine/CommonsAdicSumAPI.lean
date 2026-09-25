-- Re-export of the commons' local-degree bookkeeping for adic completions, so that lemmas
-- delegated into `Submission/Work/` can be stated in its vocabulary (`sumFinrank_eQ`,
-- `adicCompletionMap`, the local fundamental identity, the global sum formula).
import Submission.Commons.NumberTheory.NumberField.Completion.sumFinrank_adicCompletion_le_finrank
import Submission.Commons.NumberTheory.NumberField.Completion.sum_finrank_adicCompletion_eq_finrank
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver

namespace NK.Mine

/-- **The sum of the local degrees equals the global degree**, in the usable form with the
explicit index map `Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ` (the commons
theorem `sum_finrank_adicCompletion_eq_finrank` states it with a `let`-bound `e`).

For a finite extension `L / K` of number fields and a prime `Q` of `𝓞 K`:
`∑_{q | Q} [L_q : K_Q] = [L : K]`. -/
theorem sumFinrank_adicCompletion_eq_finrank {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (∑ qq : Q.asIdeal.primesOver (NumberField.RingOfIntegers L),
        @Module.finrank (Q.adicCompletion K)
          ((Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ (K := K) (L := L) Q
              qq).adicCompletion L) _ _
          (RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q
            (Commons.NumberTheory.NumberField.Completion.sumFinrank_eQ (K := K) (L := L) Q qq)
            qq.2.2)).toModule) =
      Module.finrank K L := by
  exact Commons.NumberTheory.NumberField.Completion.sum_finrank_adicCompletion_eq_finrank
    (K := K) (L := L) Q

end NK.Mine
