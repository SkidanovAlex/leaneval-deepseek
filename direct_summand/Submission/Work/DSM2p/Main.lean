import Submission.Work.DSMap.Gaps
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.CSCompletionOne_faithfullyFlat
import Submission.Work.DSM2p.CSCompletionOne_perfectoidData
import Submission.Work.DSM2p.CSCompletionOne_frobSurj_of
import Submission.Work.DSM2p.pIntClosureOne_frobSurj_proved
import Submission.Work.DSM2p.CSCompletionOne_frobInj
import Submission.Work.DSM2p.CSCompletionOne_isSMulRegular
import Submission.Work.DSM2p.CSIntegralClosureOne_isSMulRegular

/-!
# DSM2p — the deliverable: `area_M2pos1` (single-polynomial André / Česnavičius–Scholze)

`DSMap.Gaps.area_M2pos1_proved` below has the same type as the frozen node
`DSMap.Gaps.area_M2pos1` (`Submission/Work/DSMap/Gaps.lean:155`): for a perfectoid ring
`A` (`P : DSMap.PerfectoidData p A`) and a monic polynomial `F ∈ A[T]` of positive degree,
there is a `p`-completely faithfully flat perfectoid cover `B` of `A`, with the same
`ϖ`-system, in which `F` acquires a compatible system of `p`-power roots.

The cover constructed is the one-polynomial Česnavičius–Scholze cover

`B_F = CSCompletionOne A p (P.ϖ 0) F = AdicCompletion (p) (pIntClosure p (Λ[F(T)/ϖ^m]))`,

`Λ = Lam1 A p = A[T^{1/p^∞}]`; see `One.lean` for the vocabulary and
`sources/dsmap/direct_summand_m2p_h2_design.md` for the design.  The three structural inputs
`(H1)`, `(H3)`, `hsmu` and the flatness `(H2)` are proved in the sibling modules listed in the
imports.
-/

namespace DSMap.Gaps

universe a

open Work.DSM2p

set_option synthInstance.maxHeartbeats 1600000 in
/-- **`area_M2pos1`, proved** (single-polynomial André's flatness lemma in the
Česnavičius–Scholze form).  Same type as the frozen `DSMap.Gaps.area_M2pos1`. -/
theorem area_M2pos1_proved (p : ℕ) [Fact p.Prime] (A : Type a) [CommRing A]
    (P : PerfectoidData p A) (F : Polynomial A) (hF : F.Monic) (hFd : 0 < F.natDegree) :
    ∃ (B : Type a) (_ : CommRing B) (_ : Algebra A B) (Q : PerfectoidData p B),
      (∀ k, Q.ϖ k = algebraMap A B (P.ϖ k)) ∧
      Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A)})
        (B ⧸ (Ideal.span {(p : A)}).map (algebraMap A B)) ∧
      ∃ r : ℕ → B, Polynomial.aeval (r 0) F = 0 ∧ ∀ k, r (k + 1) ^ p = r k := by
  obtain ⟨Q, hϖ, hroot⟩ :=
    Work.DSM2p.CSCompletionOne_perfectoidData A p P F hF hFd
      (Work.DSM2p.CSCompletionOne_frobSurj_of A p P F
        (Work.DSM2p.pIntClosureOne_frobSurj_proved A p P F))
      (fun x hx => Work.DSM2p.CSCompletionOne_frobInj A p P F x hx)
      (Work.DSM2p.CSCompletionOne_isSMulRegular A p P F)
  exact ⟨Work.DSM2p.CSCompletionOne A p (P.ϖ 0) F, inferInstance, inferInstance, Q, hϖ,
    Work.DSM2p.CSCompletionOne_faithfullyFlat A p P F hF hFd, hroot⟩

end DSMap.Gaps
