import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- On the inner branch (`q 0 ≤ r_J`) the layer parameter recovered by `cuspInvInner` is
`t = q 0/(2 r_J) ≥ 0`, and `p = t • bndOfU u` has sup norm `t` because `nrm (bndOfU u) = 1`. -/
theorem cuspInvInner_nrm (v : Fin 5) (q : E4) (hq : q ∈ polarBox) (h : q 0 ≤ rJ) :
    nrm (cuspInvInner v q).1 = q 0 / (2 * rJ) := by
  have hrJ : (0 : ℝ) < rJ := by norm_num [rJ]
  have hq0 : (0 : ℝ) < q 0 := by linarith [hq.1]
  have hpos : 0 < q 0 / (2 * rJ) := by positivity
  unfold cuspInvInner
  simp only [h, ite_true]
  rw [nrm_smul, nrm_bndOfU, mul_one, abs_of_pos hpos]

end Work.Cusp
