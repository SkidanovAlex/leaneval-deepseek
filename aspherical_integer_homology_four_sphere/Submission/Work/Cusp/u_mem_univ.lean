import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.uPerim_mem
import Submission.Work.Cusp.smul_bnd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The perimeter parameter `u p = uPerim (bnd p)` of an **arbitrary** point of `E2` lies in the
half-open unit interval `[0,1)`.

For `p ≠ 0` the radial projection `bnd p = (nrm p)⁻¹ • p` has sup norm `1` (`nrm_bnd`), so it lies
on `∂Sq` and `uPerim_mem` gives the bounds.  At `p = 0` we have `bnd 0 = 0` and
`uPerim 0 = (7 + 0)/8 = 7/8`, which is again in `[0,1)`. -/
theorem u_mem_univ (p : Work.Cusp.E2) : 0 ≤ Work.Cusp.u p ∧ Work.Cusp.u p < 1 := by
  rw [u]
  by_cases hp : p = 0
  · subst hp
    have hb : bnd 0 = 0 := by rw [bnd]; simp
    rw [hb]
    have hu : uPerim (0 : E2) = 7 / 8 := by simp only [uPerim]; norm_num
    rw [hu]; norm_num
  · exact uPerim_mem (nrm_bnd hp)

end Work.Cusp
