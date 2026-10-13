import Mathlib
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.frobSurj_completion
import Submission.Work.DSM2p.adicCompletion_ker_eval_one

namespace Work.DSM2p

open scoped Classical

set_option maxHeartbeats 1600000 in
/-- **Frobenius surjectivity passes from `A'_F` to its `p`-adic completion `B_F`.**

The one-polynomial specialisation of `frobSurj_completion`: the two ideals `(ϖ ^ p)` and `(p)`
agree because `ϖ ^ p = p · v` with `v` a unit of `A` (`P.unit`), and the generic transfer
`adicCompletion_frobSurj_of` (proved in `frobSurj_completion.lean`) does the rest. -/
theorem CSCompletionOne_frobSurj_of (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A)
    (h : ∀ x : ↥(CSIntegralClosureOne A p (P.ϖ 0) F), ∃ y : ↥(CSIntegralClosureOne A p (P.ϖ 0) F),
      x - y ^ p ∈ Ideal.span {algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)}) :
    ∀ x : CSCompletionOne A p (P.ϖ 0) F, ∃ y : CSCompletionOne A p (P.ϖ 0) F,
      x - y ^ p ∈ Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)} := by
  -- `(ϖ ^ p) = (p)` in `A'_F`
  have hspanA : Ideal.span {algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)}
      = Ideal.span {(p : ↥(CSIntegralClosureOne A p (P.ϖ 0) F))} := by
    obtain ⟨v, hv⟩ := P.unit
    have hkey : algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)
        = (p : ↥(CSIntegralClosureOne A p (P.ϖ 0) F)) *
          algebraMap A ↥(CSIntegralClosureOne A p (P.ϖ 0) F) (↑v : A) := by
      rw [hv, map_mul, map_natCast]
    rw [hkey, Ideal.span_singleton_mul_right_unit (IsUnit.map _ v.isUnit)]
  -- `(ϖ ^ p) = (p)` in `B_F`
  have hspanB : Ideal.span {algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)}
      = Ideal.span {(p : CSCompletionOne A p (P.ϖ 0) F)} := by
    obtain ⟨v, hv⟩ := P.unit
    have hkey : algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (P.ϖ 0 ^ p)
        = (p : CSCompletionOne A p (P.ϖ 0) F) *
          algebraMap A (CSCompletionOne A p (P.ϖ 0) F) (↑v : A) := by
      rw [hv, map_mul, map_natCast]
    rw [hkey, Ideal.span_singleton_mul_right_unit (IsUnit.map _ v.isUnit)]
  -- `(H1)` restated with `(p)` in place of `(ϖ ^ p)`
  have h' : ∀ x : ↥(CSIntegralClosureOne A p (P.ϖ 0) F),
      ∃ y : ↥(CSIntegralClosureOne A p (P.ϖ 0) F),
      x - y ^ p ∈ Ideal.span {(p : ↥(CSIntegralClosureOne A p (P.ϖ 0) F))} := by
    intro x
    obtain ⟨y, hy⟩ := h x
    exact ⟨y, by rw [← hspanA]; exact hy⟩
  intro x
  obtain ⟨y, hy⟩ := adicCompletion_frobSurj_of ↥(CSIntegralClosureOne A p (P.ϖ 0) F) p h' x
  exact ⟨y, by rw [hspanB]; exact hy⟩

end Work.DSM2p
