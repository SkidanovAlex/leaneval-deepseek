import Mathlib
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.CSCompletionPos_faithfullyFlat

namespace Work.DSM2p

set_option synthInstance.maxHeartbeats 1600000 in
theorem CSCompletionOne_faithfullyFlat_of_CSIntegralClosureOne (A : Type*) [CommRing A] (p : ℕ)
    [Fact p.Prime] (P : DSMap.PerfectoidData p A) (F : Polynomial A)
    (h : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
      (↥(CSIntegralClosureOne A p (P.ϖ 0) F) ⧸
        (Ideal.span {(p : A)}).map (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F)))) :
    Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
      (CSCompletionOne A p (P.ϖ 0) F ⧸
        (Ideal.span {(p : A)}).map (algebraMap A (CSCompletionOne A p (P.ϖ 0) F))) := by
  -- `B_F = AdicCompletion (p) A'` with `A' = CSIntegralClosureOne A p (P.ϖ 0) F`, and the
  -- reduction modulo `p` of the `p`-adic completion is the reduction of `A'` itself:
  -- `B_F ⧸ pB_F ≅ A' ⧸ pA'` as `A ⧸ (p)`-algebras (`adicCompletion_quot_span_p_algEquiv`).
  -- Faithful flatness transfers along this algebra equivalence.
  haveI := h
  exact Module.FaithfullyFlat.of_linearEquiv (A ⧸ Ideal.span {(p : A)})
    (↥(CSIntegralClosureOne A p (P.ϖ 0) F) ⧸
      (Ideal.span {(p : A)}).map (algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F)))
    (adicCompletion_quot_span_p_algEquiv A p (↥(CSIntegralClosureOne A p (P.ϖ 0) F))).toLinearEquiv

end Work.DSM2p
