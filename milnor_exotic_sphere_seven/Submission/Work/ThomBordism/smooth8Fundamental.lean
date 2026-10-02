import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.excludedMV
import Submission.Work.ThomBordism.convexLocalIso
import Submission.Work.ThomBordism.convexCover
import Submission.Work.ThomBordism.localGeneration
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.capped_localDegree_generator
import Submission.Work.Cohomology.isZero_relSubPunctured
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.local_generator_ball
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

set_option backward.isDefEq.respectTransparency true in
theorem smooth8Fundamental : Work.ThomBordism.Smooth8Fundamental := by
  intro M hc0 x
  have h := localGeneration 8 (by norm_num) (TopCat.of M.pt) M.c M.c_generates hc0 x
  exact h

end

end Work.ThomBordism
