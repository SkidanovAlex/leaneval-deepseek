/-
# Auxiliary definitions for the polar (and core) charts on `M̂`

The chart lemmas of the assembly area (`Work.Cusp.exists_polarChartM`, `Work.Cusp.exists_coreChartM`)
are stated against the *cover* `E2 × E2` of a filling piece and its projection to the filling piece
`W_v = SquarePt × T_v` inside `M̂`.  This file fixes the small vocabulary that is common to those
proofs:

* `mem_sq_of_nrm_lt_one`, `sqPtOf`: a point of `E2` of sup norm `< 1` is an interior point of the
  square, hence a point of `Work.Space.SquarePt`;
* `fillInterior`: the interior of the `v`-th filling piece (the layer parameter `‖p‖∞ < 1`), an open
  subset of `SquarePt × T_v` on which the inclusion `incW v` into `M̂` is an open embedding (the
  glued boundary `‖p‖∞ = 1` is what makes `incW v` fail to be open);
* `fillProj`: the projection `(p, y) ↦ (p, tor.symm y)` of the cover onto the filling piece; this is
  the map whose openness is the "wedge of the covering map" input of the charts.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.Assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology
open scoped Real InnerProductSpace

namespace Work.Cusp

/-- **A point of `E2` of sup norm `< 1` lies in the square** `Work.Space.Sq = [-1,1]²`: both
coordinates are bounded by the sup norm. -/
theorem mem_sq_of_nrm_lt_one {p : E2} (h : nrm p < 1) : p ∈ Work.Space.Sq :=
  ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) h),
   le_of_lt (lt_of_le_of_lt (le_max_right _ _) h)⟩

/-- The point of the square `SquarePt` associated with a point of `E2` of sup norm `< 1`. -/
def sqPtOf (p : E2) (h : nrm p < 1) : Work.Space.SquarePt :=
  ⟨p, mem_sq_of_nrm_lt_one h⟩

/-- **The interior of the `v`-th filling piece**: the points of `SquarePt × T_v` with layer
parameter `‖p‖∞ < 1`, i.e. away from the glued boundary `‖p‖∞ = 1`.  It is open, and `incW v` is an
open embedding on it. -/
def fillInterior (a : Work.Space.Assembly) (v : Work.Space.Cusp) :
    Set (Work.Space.SquarePt × a.Torus v) :=
  {p | Work.Space.sqNorm p.1 < 1}

/-- **The projection of the cover `E2 × E2` of the filling piece onto the filling piece**: the layer
point `p` of sup norm `< 1` becomes a point of the square, and the real torus coordinates `y` are
reduced modulo `ℤ²` along the homeomorphism `tor`. -/
def fillProj (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (z : {z : E2 × E2 // nrm z.1 < 1}) : Work.Space.SquarePt × a.Torus v :=
  (sqPtOf z.1.1 z.2, tor.symm (fun i => ((z.1.2 i : ℝ) : AddCircle (1 : ℝ))))

end Work.Cusp
