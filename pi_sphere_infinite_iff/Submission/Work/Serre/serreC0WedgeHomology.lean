import Mathlib
import Submission.Work.Serre.serreC0Defs
import Submission.Work.Serre.serreC0Cover
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Serre.Wedge.Main

namespace Work.Serre

theorem serreC0WedgeHomology (n : ℕ) (I : Type) :
    Nonempty (((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.RatHurewicz.attachCells n PUnit I
          (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere n) PUnit.unit)))).homology (n+2)) ≅
      (∐ fun _ : I => ModuleCat.of ℤ ℤ)) :=
  Work.Serre.Wedge.wedgeHomology n I

end Work.Serre
