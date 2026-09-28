import Mathlib
import Submission.Work.Serre.serreC0Defs
import Submission.Work.Serre.serreC0Cover
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Serre.Wedge.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre

theorem serreC0WedgeHomology (n : ℕ) (I : Type) :
    Nonempty (((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.RatHurewicz.attachCells n PUnit I
          (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere n) PUnit.unit)))).homology (n+2)) ≅
      (∐ fun _ : I => ModuleCat.of ℤ ℤ)) :=
  Work.Serre.Wedge.wedgeHomology n I

end Work.Serre
