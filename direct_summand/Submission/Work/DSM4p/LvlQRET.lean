import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.lvl_kernel
import Submission.Work.DSM4p.lvl_cokernel
import Submission.Work.DSM4p.qretKernel_mono
import Submission.Work.DSM4p.qretCoker_mono

/-!
# DSM4p — `IsQRETp` for the untilted tower (kernel + cokernel, constants merged)

The two clauses of `DSMap.Mix2.IsQRETp` for the Route U tower `D n = lvl Q hgr n` are
`Work.DSM4p.lvl_kernel` (kernel, with the level bound `m·p^(k+m+3)`) and
`Work.DSM4p.lvl_cokernel` (cokernel, with an existential pro constant).  Both are monotone in the
common constant (`Work.DSM4p.qretKernel_mono`, `Work.DSM4p.qretCoker_mono`), so taking the maximum
of the two constants gives the single uniform constant required by `IsQRETp`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open DSMap DSMap.Mix DSMap.Mix2

namespace Work.DSM4p

universe a

/-- **The pro-uniform quantitative Riemann extension condition for the untilted tower.**  The
kernel clause comes from `lvl_kernel` at the level `n + c` with `c := m * p^(k+m+3)`, the cokernel
clause from `lvl_cokernel`, and the two constants are merged with the monotonicity lemmas. -/
theorem lvl_isQRETp {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr) (hgr0 : gr 0 ≠ 0) :
    IsQRETp p B Q.ϖ gr (fun n => lvl Q hgr n) (lvlTrAlg Q hgr) := by
  intro m k
  obtain ⟨cc, hc⟩ := lvl_cokernel Q hgr hgr0 m k
  refine ⟨max (m * p ^ (k + m + 3)) cc, ?_, ?_⟩
  · refine qretKernel_mono (p := p) Q.ϖ gr (lvlTrAlg Q hgr) (le_max_left _ _) ?_
    intro n x hx
    exact lvl_kernel Q hgr hgr0 k m (n + (m * p ^ (k + m + 3)))
      (by omega) x hx
  · exact qretCoker_mono (p := p) Q.ϖ gr (lvlTrAlg Q hgr) (le_max_right _ _) hc

end Work.DSM4p
