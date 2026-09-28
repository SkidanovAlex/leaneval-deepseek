import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.homology_prod_contractible
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.CompatTrans.sphere3DiscPairHomology

namespace Work.Cohomology

theorem sph3DiscRelHomology (n : ℕ) :
    Nonempty (((Work.Cohomology.relChains Work.Cohomology.PairXT Work.Cohomology.PairAT).homology n)
      ≅ ModuleCat.of ℤ (Fin ((if n = 4 then 1 else 0) + (if n = 7 then 1 else 0)) → ℤ)) := by
  exact Work.Cohomology.sphere3DiscPairHomology n

end Work.Cohomology
