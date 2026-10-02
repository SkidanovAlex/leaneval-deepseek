/-
# `Work.MandelFinal.Classical` — the classical inputs of the final assembly

Area `Submission/Work/MandelFinal/` (the final assembly of `mandelbar_not_path_connected`).

The four *classical* fields of `Work.Final.FinalInputs` — `nakane`, `gm`, `repAngle`,
`repAngle_quarter` — are **discharged** here from the delivered areas:

* `nakane`  ← `Work.NAKANE.nakaneInput_of_localHomeo`, i.e. Nakane's homeomorphism
  `Work.NAKANE.nakaneHomeo_of_localHomeo` at the **proved** `(R1)` `Work.NAKANE2.phiLocalHomeo`,
  together with the **unconditional** `Work.NAKANE.uniformBottcherAsymptotic`;
* `gm`      ← `Work.LandLeaves.repellingRayParamStable`, i.e. Goldberg–Milnor B.1
  (`Work.LandLeaves.goldbergMilnorB1`) with its scope input `DynBottcherOnlyOnMandelbar`
  (`Work.LandLeaves.dynBottcherOnlyOnMandelbar`) discharged;
* `repAngle` ← `Work.LandLeaves.paramAngleRepelling_of_rootArc_final`: Milnor 18.10
  (`Work.LandLeaves.periodicRaysLand`, proved *without* local connectivity), the Snail lemma
  (`Work.LandLeaves.snailLemmaMilnor`) and `AttractingCyclesInner`
  (`Work.LandLeaves.attractingCyclesInner`) are all proved; the only remaining input is Fatou's
  theorem on parabolic cycles at the root-arc parameter (`ParabolicCycleInOmegaLimit`);
* `repAngle_quarter` ← `Work.LandLeaves.paramAngleRepelling_quarter_final`: the remaining inputs
  are Fatou's theorem at `1/4` (`QuarterParabolicIsFixed`) and the rotation-number-zero portrait
  `Work.Landing.RotationNumberZero (1/4) 1`.

**The two remaining classical inputs, named.**  Fatou's theorem on parabolic cycles at *every*
parabolic point (including the multi-petal/degenerate ones) is the single named classical input
`Work.FatouParabolic.FatouParabolicInput`, whose *simple* half is a **theorem**
(`Work.FatouParabolic2.fatouParabolicInput_simple`); the *degenerate* half
`Work.FatouParabolic2.FatouParabolicInput_degenerate` is not on disk.  It gives both
`ParabolicCycleInOmegaLimit` and `QuarterParabolicIsFixed`
(`Work.FatouParabolic2.parabolicCycleInOmegaLimit_of_degenerate`,
`Work.FatouParabolic2.quarterParabolicIsFixed_of_degenerate`), and hence both `repAngle` and the
first half of `repAngle_quarter`.  The **rotation-number-zero portrait at `1/4`**
(`RotationNumberZero (1/4) 1`, repaired to `Int.fract` by `Work.LandLeaves`) has *no producer* in
the workspace; it is the one input of the assembly that is neither a live area's output nor a
named classical input.
-/
import Submission.Work.FinalFix.RootExport
import Submission.Work.NAKANE.NakaneInput
import Submission.Work.NAKANE2.Main
import Submission.Work.LandLeaves.Final
import Submission.Work.LandLeaves.Rows
import Submission.Work.FatouParabolic2.parabolicCycleInOmegaLimit_of_simple
import Submission.Work.FatouParabolic2.quarterParabolicIsFixed_of_simple
import Submission.Work.MandelFinal.rotationNumberZero_quarter
import Submission.Work.FatouParabolic.Reduction
import Submission.Work.FatouParabolic.Quarter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.MandelFinal

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Nakane's parameter Böttcher coordinate -/

/-- **`nakane`, the field of `Work.Final.FinalInputs`.**  Nakane's homeomorphism of the parameter
plane `Φ : Mbᶜ → exteriorDisc` (with `(R1)` discharged by `Work.NAKANE2.phiLocalHomeo`), the
Böttcher-existence field discharged by `Work.Bottcher.bottcherExists_crit`, and the
**unconditional** uniform asymptotic `Work.NAKANE.uniformBottcherAsymptotic`. -/
theorem nakaneInput : Work.ParamRays.NakaneInput :=
  Work.NAKANE.nakaneInput_of_localHomeo Work.NAKANE2.phiLocalHomeo

/-! ## Goldberg–Milnor B.1 -/

/-- **`gm`, the field of `Work.Final.FinalInputs`**: Goldberg–Milnor B.1 in parameter form, from
the parameter Böttcher map `nakaneInput`.  Its scope input `DynBottcherOnlyOnMandelbar` is the
theorem `Work.LandLeaves.dynBottcherOnlyOnMandelbar`. -/
theorem repellingRayParamStable : Work.FSeed.RepellingRayParamStable :=
  Work.LandLeaves.repellingRayParamStable nakaneInput

/-! ## Fatou's theorem on parabolic cycles -/

/-- Fatou's theorem on parabolic cycles at every period, from the **degenerate** half
`FatouParabolicInput_degenerate` of the classical input (its simple half is the theorem
`Work.FatouParabolic2.fatouParabolicInput_simple`). -/
theorem parabolicCycleInOmegaLimit
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate) (c : ℂ) :
    Work.LANDCL.ParabolicCycleInOmegaLimit c :=
  Work.FatouParabolic2.parabolicCycleInOmegaLimit_of_degenerate hDeg c

/-- The same input at `1/4`: every parabolic point of `T_{1/4}` is fixed. -/
theorem quarterParabolicIsFixed
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate) :
    Work.LANDCL.QuarterParabolicIsFixed :=
  Work.FatouParabolic2.quarterParabolicIsFixed_of_degenerate hDeg

/-! ## The two Landing rows -/

/-- **`repAngle`, the field of `Work.Final.FinalInputs` at a root arc `A`**: the parameter ray of
the window angle `23/63` lands at a repelling periodic point at the parameter of `A`.

All the Landing machinery is proved elsewhere (`Work.LandLeaves`): the landing theorem
`Work.LandLeaves.periodicRaysLand` (Milnor 18.10, *without* local connectivity), the Snail lemma
`Work.LandLeaves.snailLemmaMilnor`, and `Work.LandLeaves.attractingCyclesInner`.  The only input
is Fatou's theorem on parabolic cycles at the parameter, plus `c ∈ Mandelbar` (a field of the
root-arc data). -/
theorem paramAngleRepelling
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate) {c : ℂ}
    (A : Work.Final.RootArc c) : Work.Final.ParamAngleRepelling c :=
  Work.LandLeaves.paramAngleRepelling_of_rootArc_final A A.mem_Mandelbar
    (parabolicCycleInOmegaLimit hDeg c)

/-- **`repAngle_quarter`, the field of `Work.Final.FinalInputs` at `1/4`** — with **every** input
discharged: the Landing machinery (`Work.LandLeaves.paramAngleRepelling_quarter_final`), Fatou's
theorem at `1/4` (`quarterParabolicIsFixed`, from the degenerate half of the classical input) and
the rotation-number-zero portrait `Work.Landing.RotationNumberZero (1/4) 1` (the proved
`Work.MandelFinal.rotationNumberZero_quarter`). -/
theorem paramAngleRepelling_quarter
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate) :
    Work.Final.ParamAngleRepelling (1 / 4 : ℂ) :=
  Work.LandLeaves.paramAngleRepelling_quarter_final Work.ParamRays.quarter_mem
    (quarterParabolicIsFixed hDeg) rotationNumberZero_quarter

/-- The same, with the rotation-number-zero portrait left as a hypothesis (for callers who prefer to
supply their own instance; it is implied by `rotationNumberZero_quarter`). -/
theorem paramAngleRepelling_quarter_of
    (hDeg : Work.FatouParabolic2.FatouParabolicInput_degenerate)
    (hrz : Work.Landing.RotationNumberZero (1 / 4 : ℂ) 1) :
    Work.Final.ParamAngleRepelling (1 / 4 : ℂ) :=
  Work.LandLeaves.paramAngleRepelling_quarter_final Work.ParamRays.quarter_mem
    (quarterParabolicIsFixed hDeg) hrz

/-- Fatou's theorem on parabolic cycles at every period, from the **general** classical input
`Work.FatouParabolic.FatouParabolicInput` (the form in which the ledger states it).  The simple
half of that input is a theorem (`Work.FatouParabolic2.fatouParabolicInput_simple`), so this is
equivalent to `parabolicCycleInOmegaLimit`; it is offered for callers who hold the general form. -/
theorem parabolicCycleInOmegaLimit_of_fatou
    (hF : Work.FatouParabolic.FatouParabolicInput) (c : ℂ) :
    Work.LANDCL.ParabolicCycleInOmegaLimit c :=
  Work.FatouParabolic.parabolicCycleInOmegaLimit hF c

/-- The same at `1/4`, from the general classical input. -/
theorem quarterParabolicIsFixed_of_fatou
    (hF : Work.FatouParabolic.FatouParabolicInput) :
    Work.LANDCL.QuarterParabolicIsFixed :=
  Work.FatouParabolic.quarterParabolicIsFixed hF

end Work.MandelFinal
