import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.cuspInvInner_nrm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **`cuspInvInner` lands in the polar stratum on the inner branch.**

For `q` in the polar box `1/4 < q 0 < r_J + 1` with `q 0 ≤ r_J` the recovered layer parameter is
`t = q 0/(2 r_J)`, so the sup norm of the first component `t • bndOfU u` is `t` (`cuspInvInner_nrm`,
using `nrm (bndOfU u) = 1`).  The two inequalities `1/24 < t ≤ 1` are exactly `q 0 > 1/4` (from the
box) and `q 0 ≤ 2 r_J = 6` (from `q 0 ≤ r_J`), so `p` lies in `polarStratum`. -/
theorem cuspInvInner_mem_polarStratum (v : Fin 5) (q : E4) (hq : q ∈ polarBox) (h : q 0 ≤ rJ) :
    (cuspInvInner v q).1 ∈ polarStratum := by
  have hrJ : (0 : ℝ) < rJ := by norm_num [rJ]
  rw [polarStratum, Set.mem_ofPred_eq, cuspInvInner_nrm v q hq h]
  constructor
  · -- `1/24 < q 0/(2 r_J)`: equivalent (multiplying by `2 r_J > 0`) to `1/4 < q 0`
    have : (1 : ℝ) / 24 < 1 / 4 := by norm_num
    have := hq.1
    unfold rJ at *
    linarith
  · -- `q 0/(2 r_J) ≤ 1`: equivalent to `q 0 ≤ 2 r_J = 6`
    have := h
    unfold rJ at *
    linarith

end Work.Cusp
