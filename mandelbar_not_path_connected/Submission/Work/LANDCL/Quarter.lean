/-
Copyright: subproject `Submission/Work/LANDCL/` of `mandelbar_not_path_connected`.

# `repAngle_quarter` : the window ray at `c = 1/4`

Row `repAngle_quarter` of the delivery table: `Work.Final.ParamAngleRepelling (1/4)`.  At the
period-`1` parabolic parameter `c = 1/4` the unique parabolic cycle of `T_{1/4}` is the *fixed*
point `1/2` of the period-`1` hyperbolic component (`Work.LANDCL.QuarterParabolicIsFixed`), at
which the second return map `Tsq` has multiplier `1` (recovered from the fixed-point condition
by `Work.LANDCL.isParabolic_one_of_fixed`).  Hence a parabolic landing point of `R(23/63)` would
be the second-return fixed point `1/2`, and by rotation number zero
(`Work.Landing.RotationNumberZero (1/4) 1`, the ray period would divide `2·1 = 2`), contradicting
the exact period `6` of `23/63` (`Work.LANDCL.not_periodicAngle_two`).  So the landing point is
repelling.

**Repair (area `LandLeaves`).**  `Work.Landing.RotationNumberZero` used to conclude the
*unnormalised* `PeriodicAngle θ (2 * k)`; since `landsAt` is invariant under `θ ↦ θ + 1` while
`PeriodicAngle · (2*k)` is not, that statement was false for `2*k ≥ 1` (see
`Submission/Work/LandLeaves/NOTES_FALSE_RotationNumberZero.md`).  It now concludes
`PeriodicAngle (Int.fract θ) (2 * k)`.  The usage below is at the angle `θ = 23/63 ∈ [0,1)`,
where `Int.fract θ = θ`, so the conclusion is literally the previous one and the proof only gains
the rewriting step `hf`. -/
import Submission.Work.LANDCL.Defs
import Submission.Work.LANDCL.GM
import Submission.Work.LANDCL.ParamAngle
import Submission.Work.LANDCL.Quarter.isParabolic_one_of_fixed
import Submission.Work.LANDCL.Quarter.isParabolic_quarter_half
import Submission.Work.LANDCL.Quarter.not_periodicAngle_two
import Submission.Work.LANDCL.ParamAngle.paramAngleRepelling_of_classical

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LANDCL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- `1/2` is a fixed point of `T_{1/4}` (the cusp of the period-`1` hyperbolic component). -/
theorem quarter_fixed_half : Tantibar (1 / 4 : ℂ) (1 / 2 : ℂ) = 1 / 2 := by
  norm_num [LeanEval.ComplexAnalysis.Tantibar, map_ofNat]

/-- **`repAngle_quarter`.**  At `c = 1/4` the window ray `R(23/63)` lands at a repelling
periodic point, given the classical landing inputs, the uniqueness of the parabolic cycle at
`1/4` and rotation number zero at the parabolic fixed point. -/
theorem paramAngleRepelling_quarter (hper : Work.Landing.PeriodicRaysLand (1 / 4 : ℂ))
    (hdich : Work.Landing.EvenPeriodLandingDichotomy (1 / 4 : ℂ))
    (hfix : QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    Work.Final.ParamAngleRepelling (1 / 4 : ℂ) := by
  refine ParamAngle.paramAngleRepelling_of_classical hper hdich ?_
  intro m z hpar hland
  have hz : Tantibar (1 / 4 : ℂ) z = z := hfix z ⟨m, hpar⟩
  have hp1 : Work.Landing.IsParabolic (1 / 4 : ℂ) 1 z :=
    Quarter.isParabolic_one_of_fixed hz hpar
  have h2 : Work.Landing.PeriodicAngle (Int.fract Work.Landing.paramAngle) (2 * 1) :=
    hrz z hp1 Work.Landing.paramAngle hland
  -- `23/63 ∈ [0,1)`, so its canonical representative is itself
  -- (`Work.LandLeaves.rotationNumberZero_iff_Ico` records that the repaired statement is
  -- literally the old one on `[0,1)`).
  have hf : Int.fract Work.Landing.paramAngle = Work.Landing.paramAngle := by
    rw [Int.fract_eq_self]; norm_num [Work.Landing.paramAngle]
  exact Quarter.not_periodicAngle_two (by rw [← hf]; exact h2)

/-- The `hθ` clause at `c = 1/4`: the parameter ray `R(23/63)` does not accumulate at `1/4`. -/
theorem quarter_notMem_closure_paramRay_windowAngle (hgm : Work.FSeed.RepellingRayParamStable)
    (hper : Work.Landing.PeriodicRaysLand (1 / 4 : ℂ))
    (hdich : Work.Landing.EvenPeriodLandingDichotomy (1 / 4 : ℂ))
    (hfix : QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    (1 / 4 : ℂ) ∉ closure (Work.ParamRays.paramRay Work.Landing.paramAngle) :=
  notMem_closure_paramRay_windowAngle hgm
    (paramAngleRepelling_quarter hper hdich hfix hrz)

/-- **`repAngle_quarter` from the Snail lemma**: the same conclusion with the even-period landing
dichotomy derived from `Work.LANDCL.SnailDichotomy` and `Work.Landing.AttractingCyclesInner`. -/
theorem paramAngleRepelling_quarter_of_snail (hcontr : HyperbolicContraction (1 / 4 : ℂ))
    (hsnail : SnailDichotomy) (hgeo : Work.Landing.AttractingCyclesInner (1 / 4 : ℂ))
    (hfix : QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    Work.Final.ParamAngleRepelling (1 / 4 : ℂ) :=
  paramAngleRepelling_quarter
    (ParamAngle.periodicRaysLand_of_hyperbolicContraction hcontr)
    (ParamAngle.evenPeriodLandingDichotomy_of_snail hsnail hgeo) hfix hrz

end Work.LANDCL
