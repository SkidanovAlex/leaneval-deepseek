import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.sdIter_small_of_range
import Submission.Work.Whitney.sdIter_smallChain_local
import Submission.Work.Cohomology.SdIter
import Submission.Work.Cohomology.SmallChains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace Work.Whitney

/-- **The `A+C`-cycle of the rank-one model product formula is refined by subdivision.**

Let `Y` be a base, `X = Y × (ℝⁿ × ℝ)` the total space of the rank-one model product,
`A = Work.Whitney.tcmA` the set of points with nonzero *second* coordinate (the first fibre
coordinate) and `C = Work.Whitney.tcmC` the set of points with nonzero *third* coordinate (the
second fibre coordinate).  A singular `(n+1)`-chain `c` that is a chain of the small complex of the
pair `(A ∪ C, ∅)` — i.e. every simplex of `c` has its image contained in `A ∪ C` — becomes, after a
high enough iterate of the barycentric subdivision, a chain of the small complex of the pair
`(A, C)`.

This is the localised small-chains theorem `Work.Cohomology.exists_iter_small_chain_of_smallSupport`
applied to the concrete open sets `Work.Whitney.tcmA`, `Work.Whitney.tcmC`
(`Work.Whitney.isOpen_tcmA`, `Work.Whitney.isOpen_tcmC`).  Note that the localised form — unlike
`Work.Cohomology.exists_iter_small_chain` — needs no hypothesis that `A ∪ C` covers `X`, which is
exactly what is available here (`A ∪ C` omits the zero section `Y × {0}` of the rank-one model
product). -/
theorem sdIter_isSmallChain_of_AC (Y : Type) [TopologicalSpace Y] [Subsingleton Y] (n : ℕ)
    (c : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))).X (n + 1))
    (hc : Work.Cohomology.IsSmallChain (Work.Whitney.tcmA Y n 1 ∪ Work.Whitney.tcmC Y n 1) ∅ c) :
    ∃ N, Work.Cohomology.IsSmallChain (Work.Whitney.tcmA Y n 1) (Work.Whitney.tcmC Y n 1)
      ((Work.Cohomology.sdChainMapIter (TopCat.of (Work.Whitney.tcmX Y n 1)) N).f (n + 1) c) := by
  refine @Work.Cohomology.exists_iter_small_chain_of_smallSupport
    (TopCat.of (Work.Whitney.tcmX Y n 1))
    (Work.Whitney.tcmA Y n 1) (Work.Whitney.tcmC Y n 1)
    (Work.Whitney.isOpen_tcmA Y n 1) (Work.Whitney.isOpen_tcmC Y n 1) (n + 1) c hc

end Work.Whitney
