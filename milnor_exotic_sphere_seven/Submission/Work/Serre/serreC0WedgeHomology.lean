import Mathlib
import Submission.Work.Serre.serreC0Defs
import Submission.Work.Serre.serreC0Cover
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Serre.Wedge.Main

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

theorem serreC0WedgeHomology (n : ℕ) (I : Type) :
    Nonempty (((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.RatHurewicz.attachCells n PUnit I
          (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere n) PUnit.unit)))).homology (n+2)) ≅
      (∐ fun _ : I => ModuleCat.of ℤ ℤ)) :=
  Work.Serre.Wedge.wedgeHomology n I

end Work.Serre
