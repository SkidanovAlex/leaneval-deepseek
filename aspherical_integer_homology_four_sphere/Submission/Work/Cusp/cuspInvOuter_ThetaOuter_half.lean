/-
# The outer cusp chart `Θ_v` inverts `cuspInvOuter` on the closed collar `½ ≤ ‖p‖∞ ≤ 1`

This is the closed-collar companion of `cuspInvOuter_ThetaOuter`, which proves the round trip
`cuspInvOuter v (ThetaOuter v p y) = (p, y)` on the *open* collar `½ < ‖p‖∞ ≤ 1`.  Here the
hypothesis is weakened to `½ ≤ ‖p‖∞`: the junction level `‖p‖∞ = ½`, at which the outer chart has
height `s_J` (the `β^0 s_J^1` end of `collarHeight`), is included.

None of the ingredients of the proof needs strictness of `½ < ‖p‖∞`.  The single place the bound is
used is to know that `p ≠ 0`, so that `bndOfU (u p) = bnd p` may be applied; `½ ≤ ‖p‖∞` still gives
`nrm p ≠ 0`.  The remaining steps — the horizontal coordinates of `ThetaOuter v p y` are
`cuspX v (u p) y`, the height is `collarS v p y = collarHeight ‖p‖∞ (β x)`, the recovered layer
parameter is `‖p‖∞` because `log` of the height is affine in the layer parameter with nonzero
denominator (here `β x ≤ 3/2 < s_J`), and `nrm p • bnd p = p` — are unchanged.
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

theorem cuspInvOuter_ThetaOuter_half (v : Fin 5) (p y : E2) (hp : p ∈ Sq) (h1 : 1/2 ≤ nrm p)
    (h2 : nrm p ≤ 1) : cuspInvOuter v (ThetaOuter v p y) = (p, y) := by
  -- `‖p‖∞ ≥ 1/2` makes `p` nonzero
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
