import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `uPerim` maps `∂Sq` into `[0,1)`

The perimeter parameter `uPerim q` of a point `q` of the boundary of the square `Sq = [-1,1]²`
(invariant of the choice of edge, the four branches of the definition agreeing at the corners)
lies in the half-open unit interval `[0,1)`.  This is what makes `bndOfU` a well-defined inverse
of `uPerim ↾ ∂Sq` and gives the layer parameter `u(p)` its range.
-/

namespace Work.Cusp

theorem uPerim_mem {q : E2} (hq : nrm q = 1) : 0 ≤ uPerim q ∧ uPerim q < 1 := by
  -- `nrm q = max |q 0| |q 1| = 1`, hence both coordinates lie in `[-1,1]`.
  have hmax : max |q 0| |q 1| = 1 := by unfold nrm at hq; exact hq
  have h0 : |q 0| ≤ 1 := hmax ▸ le_max_left |q 0| |q 1|
  have h1 : |q 1| ≤ 1 := hmax ▸ le_max_right |q 0| |q 1|
  have hq0le : q 0 ≤ 1 := (abs_le.mp h0).2
  have hq0ge : -1 ≤ q 0 := (abs_le.mp h0).1
  have hq1le : q 1 ≤ 1 := (abs_le.mp h1).2
  have hq1ge : -1 ≤ q 1 := (abs_le.mp h1).1
  unfold uPerim
  by_cases hA : q 0 = 1
  · simp only [hA, ↓reduceIte]; constructor <;> nlinarith
  · simp only [hA, ↓reduceIte]
    by_cases hB : q 1 = -1
    · simp only [hB, ↓reduceIte]; constructor <;> nlinarith
    · simp only [hB, ↓reduceIte]
      by_cases hC : q 0 = -1
      · simp only [hC, ↓reduceIte]; constructor <;> nlinarith
      · simp only [hC, ↓reduceIte]
        have hq0lt : q 0 < 1 := lt_of_le_of_ne hq0le hA
        constructor <;> nlinarith

end Work.Cusp
