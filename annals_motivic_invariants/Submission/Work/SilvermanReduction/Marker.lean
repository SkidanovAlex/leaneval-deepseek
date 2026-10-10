/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.SilvermanReduction
-/
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.tateCurve_hasGoodReduction
import Submission.Work.TorsorExistence.Twist

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The marker has non-zero reduction

The last hypothesis of the class-(a) local model (`NumberFieldReduction.red_PL_ne_zero`) is that
the marker `P = (0,0)` of the Tate normal form reduces to a non-zero point.  It is a formal
consequence of `redPoint_some_mk`: the coordinates of `(0,0)` are integral (they are `0`), and a
reduction of an integral point is an affine point, never the origin.  No arithmetic is involved,
in particular no hypothesis on the residue characteristic.

## Main results

* `redPoint_some_zero_zero_ne_zero` — the reduction of `(0,0)` is non-zero.
* `tateCurve_redPoint_zero_ne_zero` — the same for the Tate normal form with a good parameter.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

/-- **The reduction of an integral point is an affine point, so `(0,0)` never reduces to `0`.** -/
theorem redPoint_some_zero_zero_ne_zero {K : Type*} [Field K] [DecidableEq K]
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (ResidueField R)]
    {W : Affine K} [W.HasGoodReduction R] (h : Nonsingular W 0 0) :
    redPoint R W (WeierstrassCurve.Affine.Point.some 0 0 h) ≠ 0 := by
  rw [redPoint_some_mk R h (r := 0) (s := 0) (by simp) (by simp)]
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- **`(0,0)` is a nonsingular point of the Tate normal form exactly when the parameter `c` is
nonzero** (the tangent at `(0,0)` is vertical precisely when `c = 0`). -/
theorem tateCurve_nonsingular_zero_zero {K : Type} [Field K]
    (c : K) (hc : c ≠ 0) : Nonsingular (Work.TorsorExistence.Tate.tateCurve c) 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  refine ⟨Work.TorsorExistence.Tate.tateCurve_equation_zero c, Or.inr ?_⟩
  simpa only [Work.TorsorExistence.Tate.tateCurve_a₃, mul_zero, zero_add] using neg_ne_zero.mpr hc

/-- **The marker of the Tate normal form reduces non-trivially**, whenever the curve has good
reduction at the place and the parameter is a unit.  This discharges the field
`NumberFieldReduction.red_PL_ne_zero` for the concrete curve of class (a). -/
theorem tateCurve_redPoint_zero_ne_zero {K : Type} [Field K] [DecidableEq K]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (ResidueField R)]
    (c : K) [hW : (Work.TorsorExistence.Tate.tateCurve c).HasGoodReduction R] (hc : c ≠ 0) :
    redPoint R (Work.TorsorExistence.Tate.tateCurve c)
        (WeierstrassCurve.Affine.Point.some 0 0 (tateCurve_nonsingular_zero_zero c hc)) ≠ 0 :=
  redPoint_some_zero_zero_ne_zero R (tateCurve_nonsingular_zero_zero c hc)

/-- **The marker of a twist `D` reduces non-trivially whenever it is the base change of `(0,0)`.**
This is the field `LocalModelData.red_PL_ne_zero` of the class-(a) residual: for the concrete curve
of `TateCurve.lean` the hypothesis `hPL` is supplied by `tateFiveTorsionCurve_PL`. -/
theorem redPoint_PL_ne_zero_of_eq_some_zero {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜)
    {h' : Nonsingular (D.E.baseChange D.ext.L) 0 0}
    (hPL : D.PL = WeierstrassCurve.Affine.Point.some 0 0 h')
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R D.ext.L] [IsFractionRing R D.ext.L]
    [DecidableEq (ResidueField R)]
    [hW : (D.E.baseChange D.ext.L).HasGoodReduction R] :
    redPoint R (D.E.baseChange D.ext.L) D.PL ≠ 0 := by
  rw [hPL]
  exact redPoint_some_zero_zero_ne_zero R h'

end

end Work.SilvermanReduction
