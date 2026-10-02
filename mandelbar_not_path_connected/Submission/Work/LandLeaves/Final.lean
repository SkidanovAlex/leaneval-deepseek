/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The ledger items 2–5 discharged, and the rows `repAngle` / `repAngle_quarter` assembled

This file records what the area actually delivers, with **no hypotheses left** beyond the parameter
data.

* **Item 5 is unconditional.**  Milnor's Snail lemma (Lemma 13.2) is proved
  (`Work.LandLeaves.snailLemmaMilnor`), the instance at periodic rays is proved
  (`Work.LandLeaves.noNeutralLanding_of_snailMilnor`), and the assembly
  `SnailLemmaMilnor → NoNeutralLanding → SnailDichotomy` is proved
  (`Work.LandLeaves.noNeutralLanding_of_snailLemmaMilnor`,
  `Work.LandLeaves.snailDichotomy_of_snailLemmaMilnor`).  Consequently

  ```lean
  theorem Work.LandLeaves.snailDichotomy : Work.LANDCL.SnailDichotomy          -- no hypotheses
  theorem Work.LandLeaves.evenPeriodLandingDichotomy (c) :
      Work.Landing.EvenPeriodLandingDichotomy c                                -- no hypotheses
  ```

  (the second from `Work.LANDCL.ParamAngle.evenPeriodLandingDichotomy_of_snail` together with the
  proved `Work.LandLeaves.attractingCyclesInner`), for **every** period — the even-period clause of
  the ledger's statement is exactly `NoNeutralLanding` and is covered.

* **Item 4 is unconditional** (`c ∈ Mandelbar`): `Work.LandLeaves.periodicRaysLand`.

* **Item 3 is unconditional** for every parameter: `Work.LandLeaves.attractingCyclesInner`.

* **Item 2 is unconditional**: `Work.LandLeaves.dynBottcherOnlyOnMandelbar`.

Hence the two delivery rows reduce to the parameter data and Fatou's theorem:

```lean
theorem Work.LandLeaves.paramAngleRepelling_of_rootArc_final (A : RootArc c) (hc : c ∈ Mandelbar)
    (homega : ParabolicCycleInOmegaLimit c) : ParamAngleRepelling c
theorem Work.LandLeaves.paramAngleRepelling_quarter_final (hc : (1/4 : ℂ) ∈ Mandelbar)
    (hfix : QuarterParabolicIsFixed) (hrz : RotationNumberZero (1/4) 1) :
    ParamAngleRepelling (1 / 4 : ℂ)
```

The only classical inputs still appearing are the ones the ledger assigns elsewhere
(`RootArc c₀` with `c₀ ∈ Mandelbar` and the `1/4`-inputs `QuarterParabolicIsFixed`,
`RotationNumberZero (1/4) 1`, `ParabolicCycleInOmegaLimit`), plus `GoldbergMilnorB1` (item 6,
delegated) for the `hθ` clause, and `NakaneInput` for the `gm` row.
-/
import Submission.Work.LandLeaves.snailLemmaMilnor
import Submission.Work.LandLeaves.noNeutralLanding
import Submission.Work.LandLeaves.Rows
import Submission.Work.LandLeaves.goldbergMilnorB1
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar

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

/-- **Ledger item 5, unconditional**: `Work.LANDCL.SnailDichotomy`.  A periodic dynamic ray whose
landing point is not attracting lands at a repelling or parabolic periodic point, for every
period — from Milnor's Snail lemma (Lemma 13.2), proved in this area. -/
theorem snailDichotomy : Work.LANDCL.SnailDichotomy :=
  snailDichotomy_of_snailLemmaMilnor snailLemmaMilnor

/-- **The even-period landing dichotomy, unconditional**: the landing point of a ray of exact
angle period `6` is repelling (for some period) or parabolic. -/
theorem evenPeriodLandingDichotomy (c : ℂ) : Work.Landing.EvenPeriodLandingDichotomy c :=
  Work.LANDCL.ParamAngle.evenPeriodLandingDichotomy_of_snail snailDichotomy
    (attractingCyclesInner c)

/-- **The `hθ` clause and `repAngle` at the root-arc parameter, from the parameter data alone**:
the root-arc data, `c ∈ Mandelbar` and Fatou's theorem on parabolic cycles give
`Work.Final.ParamAngleRepelling c`; the landing input (Milnor 18.10) and the Snail input are both
proved in this area. -/
theorem paramAngleRepelling_of_rootArc_final {c : ℂ} (A : Work.Final.RootArc c)
    (hc : c ∈ Mandelbar) (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c) :
    Work.Final.ParamAngleRepelling c :=
  paramAngleRepelling_of_rootArc_snailLemmaMilnor A hc snailLemmaMilnor
    (attractingCyclesInner c) homega

/-- **`repAngle_quarter` from the `1/4`-parameter data alone** (plus `1/4 ∈ Mandelbar`). -/
theorem paramAngleRepelling_quarter_final (hc : (1 / 4 : ℂ) ∈ Mandelbar)
    (hfix : Work.LANDCL.QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    Work.Final.ParamAngleRepelling (1 / 4 : ℂ) :=
  paramAngleRepelling_quarter_snailLemmaMilnor hc snailLemmaMilnor
    (attractingCyclesInner (1 / 4 : ℂ)) hfix hrz

/-- **The `hθ` clause at the root-arc parameter, from the parameter data alone** (Goldberg–Milnor
B.1 remains item 6). -/
theorem notMem_closure_paramRay_windowAngle_final {hgm : Work.FSeed.RepellingRayParamStable}
    {c : ℂ} (A : Work.Final.RootArc c) (hc : c ∈ Mandelbar)
    (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c) :
    c ∉ closure (Work.ParamRays.paramRay Work.Landing.paramAngle) :=
  notMem_closure_paramRay_windowAngle_landed (hgm := hgm) A hc snailLemmaMilnor
    (attractingCyclesInner c) homega

/-! ## The `gm` row and the `hθ` clause, with item 6 discharged

`Work.LANDCL.GoldbergMilnorB1` (stability of the landing at a repelling point under perturbation of
the parameter) is proved in this area (`Work.LandLeaves.goldbergMilnorB1`), and the scope input
`DynBottcherOnlyOnMandelbar` is proved (`Work.LandLeaves.dynBottcherOnlyOnMandelbar`), so the `gm`
row of the delivery table holds as soon as the parameter Böttcher map `Work.ParamRays.NakaneInput`
(NAKANE, ledger §4) is available. -/

/-- **The `gm` row**: `Work.FSeed.RepellingRayParamStable` from the parameter Böttcher map alone
(item 6 is discharged here). -/
theorem repellingRayParamStable (hN : Work.ParamRays.NakaneInput) :
    Work.FSeed.RepellingRayParamStable :=
  repellingRayParamStable_of_goldbergMilnor hN goldbergMilnorB1

/-- **The `hθ` clause of the endgame, with every LandLeaves input discharged**: the parameter ray
`R(23/63)` does not accumulate at the root-arc parameter, from the root-arc data, `c ∈ Mandelbar`,
Fatou's theorem on parabolic cycles and the parameter Böttcher map. -/
theorem notMem_closure_paramRay_windowAngle_proved {c : ℂ} (A : Work.Final.RootArc c)
    (hc : c ∈ Mandelbar) (homega : Work.LANDCL.ParabolicCycleInOmegaLimit c)
    (hN : Work.ParamRays.NakaneInput) :
    c ∉ closure (Work.ParamRays.paramRay Work.Landing.paramAngle) :=
  notMem_closure_paramRay_windowAngle_final
    (hgm := repellingRayParamStable hN) A hc homega

/-- **The `hθ` clause at `c = 1/4`, with every LandLeaves input discharged.** -/
theorem quarter_notMem_closure_paramRay_windowAngle_proved
    (hc : (1 / 4 : ℂ) ∈ Mandelbar) (hfix : Work.LANDCL.QuarterParabolicIsFixed)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) (hN : Work.ParamRays.NakaneInput) :
    (1 / 4 : ℂ) ∉ closure (Work.ParamRays.paramRay Work.Landing.paramAngle) :=
  Work.LANDCL.quarter_notMem_closure_paramRay_windowAngle (hgm := repellingRayParamStable hN)
    (periodicRaysLand (1 / 4) hc)
    (evenPeriodLandingDichotomy (1 / 4 : ℂ)) hfix hrz

end Work.LandLeaves
