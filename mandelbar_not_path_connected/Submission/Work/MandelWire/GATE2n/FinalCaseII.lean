/-
# GATE2 — the endgame: `Work.GATE.TwoSided c₀ Nm` from the sibling exports

`Work.GATE.TwoSided c₀ P.Nm` (the `twoSided` field of `Work.Final.FinalInputs`).

**This file is now a thin alias of `Work.GATE2.twoSided_of_final`**
(`Submission/Work/GATE2/FinalLast.lean`), which is the drive with the *complete* sibling-export
hypothesis list: the previous version of this file carried the four non-sibling hypotheses
`n`, `hnw`, `hnθ` (the universal `α₁`-window statement, which is **not** derivable) and `hss`
(the nest-shrinking datum, whose second conjunct needed the landing-point shrinking `hQy`).  All of
them are now produced internally; see `NOTES.md` §20 for the item-by-item account and the supplier
of every remaining hypothesis.

The branch used is the *second* one of the design's dichotomy (the real axis misses both lifts),
which is the branch that occurs at the actual `c₀`; the first branch is closed unconditionally by
`Work.GATE2.twoSided_of_realCrossing` and is derived from the nest data by the case split inside
`Work.GATE2.twoSided_of_el`.
-/
import Submission.Work.MandelWire.GATE2n.FinalLast

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
set_option maxHeartbeats 1600000

noncomputable section

namespace Work.MandelWire.G2n

open Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The `twoSided` field of the final inputs, from the sibling exports.** -/
theorem twoSided_of_data {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    (nIn : ℕ)
    (trans : ℂ → ℂ)
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P nIn c₀)).im = 0)
    (hSat : SaturatedFlower fl FF)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (him : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, (trans c).im = 0)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe)
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b)
    (hLS : Work.PARIMPL2.LockstepAll c₀ P.Nm trans nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ
      ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)))
    (hG : Work.PARIMPL.GreenEscapeOpen)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (Lray : Work.ELRig.RayCylLift d fl)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => Lray.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)))
    (hflip : Work.ELRig.FlipHyp fl nest.P0 Lray)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (hR : 3 / 2 ≤ Lray.R)
    (hPsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear nest.P0)
    (hQsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear (nest.Q n))
    (tr : Work.EL.B2Data d.hN d.z₁) :
    Work.GATE.TwoSided c₀ P.Nm :=
  twoSided_of_final (d := d) (nIn := nIn) FF trans hOpen hfront hPaeq hφa_eq hΨeq hentry₀ hcrit hSat
    hρc hcont hρh him hblowup hρe hblow hLS hG nest Lray han hflip hQa hQb hR hPsides hQsides tr

/-- **The `twoSided` field of the final inputs, from the sibling exports** — the current
deliverable of the area, under a name distinct from the older PL/EXL drive
`Work.GATE2.twoSided` of `Submission/Work/GATE2/Final.lean` (which asks for `LeakData`, `hK`,
`hHalf`, `hv`, the floored UT and the two `ExitLoop`s). -/
theorem twoSided_of_exports_pa {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    (nIn : ℕ)
    (trans : ℂ → ℂ)
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P nIn c₀)).im = 0)
    (hSat : SaturatedFlower fl FF)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (him : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, (trans c).im = 0)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe)
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b)
    (hLS : Work.PARIMPL2.LockstepAll c₀ P.Nm trans nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ
      ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)))
    (hG : Work.PARIMPL.GreenEscapeOpen)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (Lray : Work.ELRig.RayCylLift d fl)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => Lray.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)))
    (hflip : Work.ELRig.FlipHyp fl nest.P0 Lray)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (hR : 3 / 2 ≤ Lray.R)
    (hPsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear nest.P0)
    (hQsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear (nest.Q n))
    (tr : Work.EL.B2Data d.hN d.z₁) :
    Work.GATE.TwoSided c₀ P.Nm :=
  twoSided_of_data (d := d) (nIn := nIn) FF trans hOpen hfront hPaeq hφa_eq hΨeq hentry₀ hcrit hSat
    hρc hcont hρh him hblowup hρe hblow hLS hG nest Lray han hflip hQa hQb hR hPsides hQsides tr

/-- **The form requested by the wire note §B.1**: the `Pa`/`φa`/`Ψ` indirection is dropped, so the
flower's own petal, Fatou coordinate and escaping coordinate are used directly.  (`ρe`/`hρe` are
kept: they are consumed, through `gateTransitData`/`gateTransitDataAt`, to define the transit radius
`ρ = min (min (min ρc ρh) ρe) P.ρ₀` of `Work.PARIMPL.TransitData`; passing `ρe := 1`,
`hρe := one_pos` is always legitimate.) -/
theorem twoSided_of_exports {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} (nIn : ℕ) (trans : ℂ → ℂ)
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hentry₀ : Work.PARIMPL.entryPt P nIn c₀ ∈ fl.Pa)
    (hcrit : (fl.φa (Work.PARIMPL.entryPt P nIn c₀)).im = 0)
    (hSat : SaturatedFlower fl FF)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (him : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, (trans c).im = 0)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b)
    (hLS : Work.PARIMPL2.LockstepAll c₀ P.Nm trans nIn
      (fun c z => Work.PARIMPL.Ft c z) fl.Pa fl.φa fl.Ψ
      ((fl.φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)))
    (hG : Work.PARIMPL.GreenEscapeOpen)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (Lray : Work.ELRig.RayCylLift d fl)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => Lray.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)))
    (hflip : Work.ELRig.FlipHyp fl nest.P0 Lray)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (hR : 3 / 2 ≤ Lray.R)
    (hPsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear nest.P0)
    (hQsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear (nest.Q n))
    (tr : Work.EL.B2Data d.hN d.z₁) :
    Work.GATE.TwoSided c₀ P.Nm :=
  twoSided_of_exports_pa (Pa := fl.Pa) (φa := fl.φa) (Ψ := fl.Ψ) FF (nIn := nIn) trans
    hOpen hfront rfl rfl rfl hentry₀ hcrit hSat
    hρc hcont hρh him hblowup (ρe := 1) one_pos hblow hLS hG nest Lray han hflip hQa hQb hR
    hPsides hQsides tr


end Work.MandelWire.G2n
