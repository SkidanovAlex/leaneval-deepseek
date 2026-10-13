import Mathlib
import Submission.Work.DSM4p.Completion
import Submission.Work.DSM4p.Chart
import Submission.Work.DSM4p.Basic

namespace Work.DSM4p

universe a

/-
(File `Submission/Work/DSM4p/iterTr_chartComp_of.lean`, namespace `Work.DSM4p`.)
The iteration of a transition map of the completed chart levels that is compatible with
`Work.DSM4p.chartTr` in one step is compatible with the iterated chart transition in `c`
steps.  Direct induction on `c` using `Work.DSM4p.iterTr_succ_apply` (the restatement of
`DSMap.Mix.iterTr_succ_apply` in `Submission/Work/DSM4p/Basic.lean`; `DSMap.Mix.iterTr` is the
frozen `iterTr` of `Submission/Work/DSMap/Mix.lean`, the one occurring in `IsQRETp`).
-/
theorem iterTr_chartComp_of {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr) (Q : DSMap.PerfectoidData p B)
    (tr : ∀ n, Work.DSM4p.chartComp hgr Q (n + 1) →ₐ[B] Work.DSM4p.chartComp hgr Q n)
    (htr : ∀ (n : ℕ) (y : Work.DSM4p.chartRing hgr Q.ϖ (n + 1)),
        tr n (AdicCompletion.of (Ideal.span {(p : Work.DSM4p.chartRing hgr Q.ϖ (n + 1))})
            (Work.DSM4p.chartRing hgr Q.ϖ (n + 1)) y)
          = AdicCompletion.of (Ideal.span {(p : Work.DSM4p.chartRing hgr Q.ϖ n)})
              (Work.DSM4p.chartRing hgr Q.ϖ n) (Work.DSM4p.chartTr hgr Q.ϖ n y)) :
    ∀ (n c : ℕ) (y : Work.DSM4p.chartRing hgr Q.ϖ (n + c)),
      DSMap.Mix.iterTr tr n c
          (AdicCompletion.of (Ideal.span {(p : Work.DSM4p.chartRing hgr Q.ϖ (n + c))})
            (Work.DSM4p.chartRing hgr Q.ϖ (n + c)) y)
        = AdicCompletion.of (Ideal.span {(p : Work.DSM4p.chartRing hgr Q.ϖ n)})
            (Work.DSM4p.chartRing hgr Q.ϖ n) (DSMap.Mix.iterTr (Work.DSM4p.chartTr hgr Q.ϖ) n c y) := by
  -- `tr` agrees with `chartTr` on the image of the structure maps `chartRing (n+1) → chartComp (n+1)`;
  -- we transport that one-step compatibility along the iteration.
  intro n c
  induction c with
  | zero => intro y; rfl
  | succ c ih =>
    intro y
    -- The one-step hypothesis is stated at the index `n + 1`; in the induction step it is needed
    -- at the index `n + c`, i.e. for arguments living in `chartComp (n + c + 1)`, which is only
    -- definitionally equal to `chartComp (n + (c + 1))`.  Recording the transported statement
    -- explicitly lets `rw` see it in the goal.
    have hkey : tr (n + c)
          (AdicCompletion.of (Ideal.span {(p : Work.DSM4p.chartRing hgr Q.ϖ (n + (c + 1)))})
            (Work.DSM4p.chartRing hgr Q.ϖ (n + (c + 1))) y)
        = AdicCompletion.of (Ideal.span {(p : Work.DSM4p.chartRing hgr Q.ϖ (n + c))})
            (Work.DSM4p.chartRing hgr Q.ϖ (n + c))
            (Work.DSM4p.chartTr hgr Q.ϖ (n + c) y) := htr (n + c) y
    rw [Work.DSM4p.iterTr_succ_apply, hkey]
    exact ih (Work.DSM4p.chartTr hgr Q.ϖ (n + c) y)

end Work.DSM4p
