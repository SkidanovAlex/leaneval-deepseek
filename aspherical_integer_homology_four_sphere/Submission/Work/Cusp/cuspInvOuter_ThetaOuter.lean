/-
# The outer cusp chart `Θ_v` inverts `cuspInvOuter` on the collar `½ ≤ ‖p‖∞ ≤ 1`

The outer chart of blueprint §1 is the map

  `ThetaOuter v p y = (x, s)`,  `x = cuspX v (u p) y`,  `s = collarS v p y = β(x)^{2‖p‖∞−1} s_J^{2−2‖p‖∞}`,

from the filling square `Sq = [-1,1]²` (layer parameter `p`, torus coordinate `y`) to the UHS
coordinates `(x,s)`.  `cuspInvOuter v` is its explicit inverse, defined on UHS coordinates
`q = (x,s)` by

  `cuspInvOuter v q = (t • bndOfU (σ-coordinate of x), y(x))`,  `t = 1 + (log s − log β(x))/(2 (log β(x) − log s_J))`.

On the collar stratum `½ < ‖p‖∞ ≤ 1` the two round trips hold, and this file proves the one that
computes `cuspInvOuter` at the chart image:

* the three horizontal coordinates `!₂[(Θ p y) 0, (Θ p y) 1, (Θ p y) 2]` of `ThetaOuter v p y` are
  the cusp coordinate `cuspX v (u p) y`, so `outerU` and `outerY` (the explicit inverses of the
  cusp-coordinate map `cuspX`, `outerU_cuspX`/`outerY_cuspX`) return `u p` and `y`;
* the height coordinate is `collarS v p y = collarHeight ‖p‖∞ (β x)`, whose logarithm is the affine
  function `(2‖p‖∞−1) log β(x) + (2−2‖p‖∞) log s_J` of `t = ‖p‖∞`, so the recovered layer parameter
  `t = 1 + (log s − log β(x))/(2 (log β(x) − log s_J))` is `‖p‖∞` — this is where the strict
  inequality `β x ≤ β_max = 3/2 < s_J` (`beta_le_max`, `betaMax_lt_sJ`) is used, to make the
  denominator `2 (log β(x) − log s_J)` nonzero;
* finally `nrm p • bndOfU (u p) = nrm p • bnd p = p` (`bndOfU_u`, `smul_bnd`), because `p ∈ Sq` and
  `p ≠ 0` (which follows from `‖p‖∞ > 1/2`).
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.bndOfU_u
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.outerU_cuspX
import Submission.Work.Cusp.outerY_cuspX
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped RealInnerProductSpace

/-- The three horizontal coordinates of `ThetaOuter v p y` are the cusp coordinate
`cuspX v (u p) y` (the fourth coordinate being the collar height `collarS`). -/
private lemma outerH (v : Fin 5) (p y : E2) :
    (!₂[(ThetaOuter v p y) 0, (ThetaOuter v p y) 1, (ThetaOuter v p y) 2] : E3)
      = cuspX v (u p) y := by
  ext i
  fin_cases i <;> simp [ThetaOuter]

/-- The fourth coordinate of `ThetaOuter v p y` is the collar height `collarS v p y`. -/
private lemma outerV (v : Fin 5) (p y : E2) : (ThetaOuter v p y) 3 = collarS v p y := by
  simp [ThetaOuter]

theorem cuspInvOuter_ThetaOuter (v : Fin 5) (p y : E2) (hp : p ∈ Sq) (h1 : 1/2 < nrm p)
    (h2 : nrm p ≤ 1) : cuspInvOuter v (ThetaOuter v p y) = (p, y) := by
  -- `‖p‖∞ > 1/2` makes `p` nonzero
  have hne : p ≠ 0 := by
    intro h0
    have hz : nrm p = 0 := by rw [h0]; simp [nrm]
    linarith
  have hx := outerH v p y
  have h3 := outerV v p y
  -- the ceiling at `x = cuspX v (u p) y` is positive and strictly below the junction `s_J`
  have hb0 : 0 < beta (cuspX v (u p) y) := beta_pos _
  have hb1 : beta (cuspX v (u p) y) < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  have hlog : Real.log (beta (cuspX v (u p) y)) - Real.log sJ ≠ 0 :=
    sub_ne_zero.mpr (ne_of_lt (Real.log_lt_log hb0 hb1))
  have hd : (2 : ℝ) * (Real.log (beta (cuspX v (u p) y)) - Real.log sJ) ≠ 0 :=
    mul_ne_zero (by norm_num) hlog
  -- the logarithm of the collar height is affine in the layer parameter
  have hlg : Real.log (collarS v p y)
      = (2 * nrm p - 1) * Real.log (beta (cuspX v (u p) y)) + (2 - 2 * nrm p) * Real.log sJ := by
    rw [collarS, collarHeight, Real.log_exp]
  simp only [cuspInvOuter]
  rw [h3, hx, outerU_cuspX, outerY_cuspX, hlg]
  -- the recovered layer parameter is `‖p‖∞`
  have hnum : (2 * nrm p - 1) * Real.log (beta (cuspX v (u p) y)) + (2 - 2 * nrm p) * Real.log sJ
        - Real.log (beta (cuspX v (u p) y))
      = (nrm p - 1) * (2 * (Real.log (beta (cuspX v (u p) y)) - Real.log sJ)) := by ring
  rw [hnum, mul_div_cancel_right₀ _ hd,
    show 1 + (nrm p - 1) = nrm p from by ring]
  -- `nrm p • bndOfU (u p) = nrm p • bnd p = p`
  rw [bndOfU_u (p := p) hp hne, smul_bnd]

end Work.Cusp
