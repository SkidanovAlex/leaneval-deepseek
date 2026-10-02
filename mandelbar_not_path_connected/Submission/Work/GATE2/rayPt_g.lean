import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.ELTop.landsN_map

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2

open LeanEval.ComplexAnalysis (Tantibar)

/-- The antiholomorphic square root `g = (T_c)^[5]` of `F c` acts on the dynamical ray points by the fifth iterate of the angle-doubling map `T θ = -2θ mod 1` and by `t ↦ t^32`: it is the `g`-version of `Work.ELTop.rayPt_T`. -/
theorem rayPt_g {c : ℂ} (d : Work.EL.RootParabolic c) {θ t : ℝ} (ht : 1 < t) :
    (Tantibar c)^[5] (Work.EL.rayPt d.hN θ t)
      = Work.EL.rayPt d.hN ((Work.EL.T^[5]) θ) (t ^ (32 : ℕ)) := by
  rw [Work.ELRig.rayPt_iterate_antibar d.hN d.bottcher ht 5]
  norm_num

end Work.GATE2
