/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The `LANDCL` reductions consuming `PeriodicRaysLand` (ledger item 4, second half)

The rows `repAngle` and `repAngle_quarter` of the delivery table of
`Submission/Work/NOTES_LEAD_mandelbar_residuals.md` §4 were assembled in
`Submission/Work/LANDCL/ParamAngle.lean` and `.../Quarter.lean` from the *Carathéodory* route:
the existence of a continuous extension of the inverse Böttcher coordinate
(`Work.LANDCL.HyperbolicContraction c = ∃ φ, IsDynBottcherHomeo c φ ∧ InverseBottcherExtends c φ`),
which is local connectivity of the Julia set at a parabolic parameter — the class-`D` input of the
ledger §5.

This file contains the same reductions with that input **replaced by
`Work.Landing.PeriodicRaysLand c`**, the landing theorem for periodic rays as a statement about
rays only (Milnor 18.10 in its direct form: the hyperbolic metric on `ℂ ∖ closure (postcritical
set)`, no local connectivity).  `PeriodicRaysLand` is *strictly weaker* than
`HyperbolicContraction`: the latter implies it (`Work.Landing.PeriodicRaysLand_of_extension`), but
not conversely.  Nothing else in the reductions changes: the even-period dichotomy comes from the
Snail lemma (`SnailDichotomy`) plus the geometric input (`AttractingCyclesInner`), and
non-parabolicity comes from the uniqueness of the parabolic cycle
(`OnlyParabolicIsCycleOf` / `QuarterParabolicIsFixed` + `RotationNumberZero (1/4) 1`).

`paramAngleRepelling_of_rootArc_rayAccumSingleton` is the same reduction fed from the
accumulation-set form `RayAccumSingleton`, which is the shape in which the direct Milnor argument
is naturally stated (`rayAccumSingleton_iff_periodicRaysLand`).
-/
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.snailDichotomy_of_noNeutral
import Submission.Work.LandLeaves.noNeutralLanding
import Submission.Work.LANDCL.ParamAngle
import Submission.Work.LANDCL.Quarter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **`repAngle` from `PeriodicRaysLand`, with the uniqueness of the parabolic cycle**: the
root-arc data, the landing theorem for periodic rays (Milnor 18.10, direct form), the Snail lemma
and Milnor 18.10's geometric input give `Work.Final.ParamAngleRepelling c`. -/
theorem paramAngleRepelling_of_rootArc_periodicRaysLand {c : ℂ} (A : Work.Final.RootArc c)
    (hper : Work.Landing.PeriodicRaysLand c) (hsnail : Work.LANDCL.SnailDichotomy)
    (hgeo : Work.Landing.AttractingCyclesInner c)
    (huniq : Work.LANDCL.OnlyParabolicIsCycleOf c A.d.z₁) :
    Work.Final.ParamAngleRepelling c :=
  Work.LANDCL.paramAngleRepelling_of_rootArc A hper
    (Work.LANDCL.ParamAngle.evenPeriodLandingDichotomy_of_snail hsnail hgeo) huniq

/-- **`repAngle` from `PeriodicRaysLand` and Fatou's theorem on parabolic cycles**: the same with
the uniqueness of the parabolic cycle derived from `ParabolicCycleInOmegaLimit` (Fatou: every
parabolic cycle is an `ω`-limit cycle of the critical orbit). -/
theorem paramAngleRepelling_of_rootArc_periodicRaysLand_omegaLimit {c : ℂ}
    (A : Work.Final.RootArc c) (hper : Work.Landing.PeriodicRaysLand c)
    (hsnail : Work.LANDCL.SnailDichotomy) (hgeo : Work.Landing.AttractingCyclesInner c)
    (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c) :
    Work.Final.ParamAngleRepelling c :=
  paramAngleRepelling_of_rootArc_periodicRaysLand A hper hsnail hgeo
    (Work.LANDCL.onlyParabolicIsCycleOf_of_rootParabolic A.d homega)

/-- **`repAngle` from the accumulation-set form of the landing theorem** (`RayAccumSingleton`,
the conclusion of the direct Milnor 18.10 argument): this is the reduction to feed once the direct
proof of the landing theorem is available in accumulation-set form. -/
theorem paramAngleRepelling_of_rootArc_rayAccumSingleton {c : ℂ} (A : Work.Final.RootArc c)
    (hdyn : Work.ParamRays.DynBottcherExists c) (h : RayAccumSingleton c)
    (hsnail : Work.LANDCL.SnailDichotomy) (hgeo : Work.Landing.AttractingCyclesInner c)
    (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c) :
    Work.Final.ParamAngleRepelling c :=
  paramAngleRepelling_of_rootArc_periodicRaysLand_omegaLimit A
    ((rayAccumSingleton_iff_periodicRaysLand hdyn).mp h) hsnail hgeo homega

/-- **The `hθ` clause at the root-arc parameter, from `PeriodicRaysLand`** (Goldberg–Milnor B.1
applied to the repelling landing point of `R(23/63)`): the parameter ray `R(23/63)` does not
accumulate at `c`. -/
theorem notMem_closure_paramRay_windowAngle_of_rootArc {hgm : Work.FSeed.RepellingRayParamStable}
    {c : ℂ} (A : Work.Final.RootArc c) (hper : Work.Landing.PeriodicRaysLand c)
    (hsnail : Work.LANDCL.SnailDichotomy) (hgeo : Work.Landing.AttractingCyclesInner c)
    (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c) :
    c ∉ closure (Work.ParamRays.paramRay Work.Landing.paramAngle) :=
  Work.LANDCL.notMem_closure_paramRay_windowAngle hgm
    (paramAngleRepelling_of_rootArc_periodicRaysLand_omegaLimit A hper hsnail hgeo homega)

/-- **`repAngle_quarter` from `PeriodicRaysLand`**: at `c = 1/4` the unique parabolic cycle is the
fixed point `1/2` of the period-`1` component (`QuarterParabolicIsFixed`), rotation number zero
(`RotationNumberZero (1/4) 1`, in its repaired `Int.fract` form) bounds the angle period of a
parabolic landing by `2`, and `23/63` has exact period `6`. -/
theorem paramAngleRepelling_quarter_of_periodicRaysLand
    (hper : Work.Landing.PeriodicRaysLand (1 / 4 : ℂ)) (hsnail : Work.LANDCL.SnailDichotomy)
    (hgeo : Work.Landing.AttractingCyclesInner (1 / 4 : ℂ))
    (hfix : Work.LANDCL.QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    Work.Final.ParamAngleRepelling (1 / 4 : ℂ) :=
  Work.LANDCL.paramAngleRepelling_quarter hper
    (Work.LANDCL.ParamAngle.evenPeriodLandingDichotomy_of_snail hsnail hgeo) hfix hrz

/-- **`repAngle_quarter` from the accumulation-set form of the landing theorem.** -/
theorem paramAngleRepelling_quarter_of_rayAccumSingleton
    (hdyn : Work.ParamRays.DynBottcherExists (1 / 4 : ℂ)) (h : RayAccumSingleton (1 / 4 : ℂ))
    (hsnail : Work.LANDCL.SnailDichotomy)
    (hgeo : Work.Landing.AttractingCyclesInner (1 / 4 : ℂ))
    (hfix : Work.LANDCL.QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    Work.Final.ParamAngleRepelling (1 / 4 : ℂ) :=
  paramAngleRepelling_quarter_of_periodicRaysLand
    ((rayAccumSingleton_iff_periodicRaysLand hdyn).mp h) hsnail hgeo hfix hrz

/-- **The `hθ` clause at `c = 1/4`, from `PeriodicRaysLand`.** -/
theorem quarter_notMem_closure_paramRay_windowAngle_of_periodicRaysLand
    {hgm : Work.FSeed.RepellingRayParamStable}
    (hper : Work.Landing.PeriodicRaysLand (1 / 4 : ℂ)) (hsnail : Work.LANDCL.SnailDichotomy)
    (hgeo : Work.Landing.AttractingCyclesInner (1 / 4 : ℂ))
    (hfix : Work.LANDCL.QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    (1 / 4 : ℂ) ∉ closure (Work.ParamRays.paramRay Work.Landing.paramAngle) :=
  Work.LANDCL.quarter_notMem_closure_paramRay_windowAngle hgm hper
    (Work.LANDCL.ParamAngle.evenPeriodLandingDichotomy_of_snail hsnail hgeo) hfix hrz

/-! ## The same reductions fed from the Snail lemma itself

`Work.LANDCL.SnailDichotomy` is produced from `Work.LandLeaves.NoNeutralLanding` (the Snail content)
by `Work.LandLeaves.snailDichotomy_of_noNeutralLanding`; the following are the resulting
reductions, in which the even-period dichotomy therefore rests on the Snail lemma rather than on
the ledger's `SnailDichotomy` as a black box. -/

/-- **`repAngle` from `PeriodicRaysLand` and the Snail lemma.** -/
theorem paramAngleRepelling_of_rootArc_noNeutral {c : ℂ} (A : Work.Final.RootArc c)
    (hper : Work.Landing.PeriodicRaysLand c) (hsnail : NoNeutralLanding)
    (hgeo : Work.Landing.AttractingCyclesInner c)
    (huniq : Work.LANDCL.OnlyParabolicIsCycleOf c A.d.z₁) :
    Work.Final.ParamAngleRepelling c :=
  paramAngleRepelling_of_rootArc_periodicRaysLand A hper
    (snailDichotomy_of_noNeutralLanding hsnail) hgeo huniq

/-- **`repAngle` from `PeriodicRaysLand`, the Snail lemma and Fatou's theorem.** -/
theorem paramAngleRepelling_of_rootArc_noNeutral_omegaLimit {c : ℂ} (A : Work.Final.RootArc c)
    (hper : Work.Landing.PeriodicRaysLand c) (hsnail : NoNeutralLanding)
    (hgeo : Work.Landing.AttractingCyclesInner c)
    (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c) :
    Work.Final.ParamAngleRepelling c :=
  paramAngleRepelling_of_rootArc_noNeutral A hper hsnail hgeo
    (Work.LANDCL.onlyParabolicIsCycleOf_of_rootParabolic A.d homega)

/-- **`repAngle_quarter` from `PeriodicRaysLand` and the Snail lemma.** -/
theorem paramAngleRepelling_quarter_of_noNeutral
    (hper : Work.Landing.PeriodicRaysLand (1 / 4 : ℂ)) (hsnail : NoNeutralLanding)
    (hgeo : Work.Landing.AttractingCyclesInner (1 / 4 : ℂ))
    (hfix : Work.LANDCL.QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    Work.Final.ParamAngleRepelling (1 / 4 : ℂ) :=
  paramAngleRepelling_quarter_of_periodicRaysLand hper
    (snailDichotomy_of_noNeutralLanding hsnail) hgeo hfix hrz

end Work.LandLeaves

