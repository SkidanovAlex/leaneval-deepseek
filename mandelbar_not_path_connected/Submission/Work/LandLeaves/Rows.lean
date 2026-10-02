/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The `LANDCL` rows `repAngle` / `repAngle_quarter` assembled from the proved inputs

This file collects the delivery-table rows in their final form, using the results proved in this
area:

* `Work.LandLeaves.periodicRaysLand` — the Douady–Hubbard / Milnor 18.10 landing theorem for
  periodic rays, for `c ∈ Mandelbar`, *proved* here without any local-connectivity hypothesis
  (so `Work.LANDCL.HyperbolicContraction`, the class-`D` Carathéodory input, is no longer needed);
* `Work.LandLeaves.attractingCyclesInner` — the geometric input of Milnor 18.10, *proved* for every
  parameter;
* `Work.LandLeaves.snailDichotomy_of_snailLemmaMilnor` — the even-period dichotomy from Milnor's
  Snail lemma (Lemma 13.2).

The only remaining classical inputs of the two rows are therefore: the `RootArc c` / `1/4`
parameters with `c ∈ Mandelbar`, the Snail lemma `Work.LandLeaves.SnailLemmaMilnor`, Fatou's
theorem on parabolic cycles (`ParabolicCycleInOmegaLimit`), and the uniqueness of the parabolic
cycle at `1/4` together with rotation number zero there.
-/
import Submission.Work.LandLeaves.Reductions
import Submission.Work.LandLeaves.noNeutralLanding
import Submission.Work.LandLeaves.periodicRaysLand

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

/-! ## The rows assembled from the *proved* landing theorem

`PeriodicRaysLand c` for `c ∈ Mandelbar` is proved in this area
(`Work.LandLeaves.periodicRaysLand`, the Douady–Hubbard/Milnor 18.10 landing theorem for periodic
rays, obtained without any local-connectivity hypothesis), and `Work.Landing.AttractingCyclesInner`
is proved for every parameter (`Work.LandLeaves.attractingCyclesInner`).  Hence the two rows of the
delivery table reduce to the following concrete inputs:

* `repAngle`: a `RootArc c`, `c ∈ Mandelbar`, the Snail lemma (Milnor 13.2) and Fatou's theorem on
  parabolic cycles;
* `repAngle_quarter`: `1/4 ∈ Mandelbar`, the Snail lemma, `QuarterParabolicIsFixed` and
  `RotationNumberZero (1/4) 1`. -/

/-- **`repAngle`, from the proved landing theorem.** -/
theorem paramAngleRepelling_of_rootArc_landed {c : ℂ} (A : Work.Final.RootArc c)
    (hc : c ∈ Mandelbar) (hsnail : Work.LANDCL.SnailDichotomy)
    (hgeo : Work.Landing.AttractingCyclesInner c)
    (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c) :
    Work.Final.ParamAngleRepelling c :=
  paramAngleRepelling_of_rootArc_periodicRaysLand_omegaLimit A (periodicRaysLand c hc)
    hsnail hgeo homega

/-- **`repAngle`, from the proved landing theorem and the Snail lemma alone**: no classical
`SnailDichotomy` black box, only Milnor's Lemma 13.2 (`Work.LandLeaves.SnailLemmaMilnor`). -/
theorem paramAngleRepelling_of_rootArc_snailLemmaMilnor {c : ℂ} (A : Work.Final.RootArc c)
    (hc : c ∈ Mandelbar) (h : SnailLemmaMilnor)
    (hgeo : Work.Landing.AttractingCyclesInner c)
    (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c) :
    Work.Final.ParamAngleRepelling c :=
  paramAngleRepelling_of_rootArc_landed A hc (snailDichotomy_of_snailLemmaMilnor h) hgeo homega

/-- **`repAngle_quarter`, from the proved landing theorem.** -/
theorem paramAngleRepelling_quarter_landed (hc : (1 / 4 : ℂ) ∈ Mandelbar)
    (hsnail : Work.LANDCL.SnailDichotomy)
    (hgeo : Work.Landing.AttractingCyclesInner (1 / 4 : ℂ))
    (hfix : Work.LANDCL.QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    Work.Final.ParamAngleRepelling (1 / 4 : ℂ) :=
  paramAngleRepelling_quarter_of_periodicRaysLand (periodicRaysLand (1 / 4) hc) hsnail hgeo hfix hrz

/-- **`repAngle_quarter`, from the proved landing theorem and the Snail lemma alone.** -/
theorem paramAngleRepelling_quarter_snailLemmaMilnor (hc : (1 / 4 : ℂ) ∈ Mandelbar)
    (h : SnailLemmaMilnor) (hgeo : Work.Landing.AttractingCyclesInner (1 / 4 : ℂ))
    (hfix : Work.LANDCL.QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    Work.Final.ParamAngleRepelling (1 / 4 : ℂ) :=
  paramAngleRepelling_quarter_landed hc (snailDichotomy_of_snailLemmaMilnor h) hgeo hfix hrz

/-- **The `hθ` clause at the root-arc parameter, from the proved landing theorem.** -/
theorem notMem_closure_paramRay_windowAngle_landed {hgm : Work.FSeed.RepellingRayParamStable}
    {c : ℂ} (A : Work.Final.RootArc c) (hc : c ∈ Mandelbar) (h : SnailLemmaMilnor)
    (hgeo : Work.Landing.AttractingCyclesInner c)
    (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c) :
    c ∉ closure (Work.ParamRays.paramRay Work.Landing.paramAngle) :=
  Work.LANDCL.notMem_closure_paramRay_windowAngle hgm
    (paramAngleRepelling_of_rootArc_snailLemmaMilnor A hc h hgeo homega)


end Work.LandLeaves
