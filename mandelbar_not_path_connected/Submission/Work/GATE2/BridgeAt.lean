/-
# GATE2 — the drive with a *chosen* leak centre (no `LeakData`)

`Work.GATE2.twoSided_of_trans_exitPath` (`Submission/Work/GATE2/Bridge.lean`) takes PARIMPL's
`LeakData` in order to *name* the leak centre `L.xstar − L.j₀` and the radius `L.r₀`; nothing else
of the bundle is used on this path (`Relay.gateTransitData` takes the escape as a hypothesis about
`trans`, since `LeakData.escape` is stated for `transU` and `LockstepAll … transU …` is not
available).  This module records the parameterised form: the centre `xLeak`, the radius `r₀` and
its positivity `hr₀` are **arguments**.

This is the form the design's case-(ii) drive needs (`NOTES_LEAD_mandelbar_gaps3.md` §2.2), where
GATE2 chooses the leak centre itself (the last real point of the lifted equipotential arc).
-/
import Submission.Work.GATE2.FreeLeak
import Submission.Work.GATE2.ExitPath

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The `twoSided` field of `Work.Final.FinalInputs` from an *arbitrary* leak centre.**  The
single residual beyond the transit data and the two exit-path data is the `ExitPathData` of the two
tongues at the chosen centre — the design's D1. -/
theorem twoSided_of_trans_exitPathAt {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d}
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (xLeak r₀ : ℝ) (hr₀ : 0 < r₀) (trans : ℂ → ℂ)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ r₀ / 8)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe)
    (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = xLeak ∨ y = xLeak + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < r₀ / 2 → c ∉ Mandelbar)
    (h₁ : ExitPathData c₀ P.Nm trans xLeak r₀
      (fun e => Work.GATE.bTongue trans xLeak r₀ e) Work.EL.alpha1)
    (h₂ : ExitPathData c₀ P.Nm trans xLeak r₀
      (fun e => Work.GATE.iotaTongue trans xLeak r₀ e) Work.EL.alpha2) :
    Work.GATE.TwoSided c₀ P.Nm :=
  twoSided_of_exitPath hOpen hfront
    (gateTransitDataAt (P := P) xLeak r₀ hr₀ trans hρc hcont hρh hheight hblowup hρe hesc)
    h₁ h₂

end Work.GATE2
