import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.homology_prod_contractible
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.CompatTrans.sphere3DiscPairHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

theorem sph3DiscRelHomology (n : ℕ) :
    Nonempty (((Work.Cohomology.relChains Work.Cohomology.PairXT Work.Cohomology.PairAT).homology n)
      ≅ ModuleCat.of ℤ (Fin ((if n = 4 then 1 else 0) + (if n = 7 then 1 else 0)) → ℤ)) := by
  exact Work.Cohomology.sphere3DiscPairHomology n

end Work.Cohomology
