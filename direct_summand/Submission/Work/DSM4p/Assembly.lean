import Submission.Work.DSM4p.Reduction
import Submission.Work.DSM4p.chartCokernel

/-!
# DSM4p — the chart tower satisfies `IsQRETp` modulo its kernel clause

`Work.DSM4p.chartCokernel` proves the cokernel clause of the pro-uniform QRET condition for
the chart tower `D n = chartLevel hgr Q.ϖ n ⊆ B[1/g]` at the uniform constant
`c = retC p k m = p^(k+1)·m` (Bhatt, arXiv:1608.08882, Theorem 3.1(2)).  Feeding it into the
reduction `Work.DSM4p.isQRETAt_chartTower` of `DSM4p/Reduction.lean` isolates the *kernel*
clause `Work.DSM4p.ChartKernel` as the single remaining input:

  `isQRETp_chartTower_of_kernel : (∀ m k, ChartKernel Q gr hgr m k) → IsQRETp … chartTower`.

The two things that still separate this from the frozen node `DSMap.Mix2.area_M4p` are
(1) the `PerfectoidData` structure on the levels of the tower — the chart levels are
`p`-torsion-free (`chartLevel_torsionFree`) with the divisibility `g ∣ p^n`
(`chartLevel_dvd`) but not complete, so the levels of the node have to be their `ϖ`-adic
completions, identified with the chart rings modulo `p^m` by Scholze's Lemma 6.4 — and
(2) the kernel clause itself.  See the module docstring of `DSM4p/Main.lean`.
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]

/-- The chart tower satisfies `IsQRETAt` at level `(m, k)` as soon as its kernel clause does:
the cokernel clause is `Work.DSM4p.chartCokernel`. -/
theorem isQRETAt_chartTower_of_kernel (Q : PerfectoidData p B) (gr : ℕ → B)
    (hgr : IsRootSystem p gr) (m k : ℕ) (hk : ChartKernel Q gr hgr m k) :
    IsQRETAt p B Q.ϖ gr (chartRing hgr Q.ϖ) (chartTr hgr Q.ϖ) m k :=
  isQRETAt_chartTower Q gr hgr m k hk (chartCokernel Q gr hgr m k)

/-- The chart tower satisfies the pro-uniform QRET condition `IsQRETp` as soon as its kernel
clause holds at every level. -/
theorem isQRETp_chartTower_of_kernel (Q : PerfectoidData p B) (gr : ℕ → B)
    (hgr : IsRootSystem p gr) (hk : ∀ m k, ChartKernel Q gr hgr m k) :
    IsQRETp p B Q.ϖ gr (chartRing hgr Q.ϖ) (chartTr hgr Q.ϖ) :=
  fun m k => isQRETAt_chartTower_of_kernel Q gr hgr m k (hk m k)

end Work.DSM4p
