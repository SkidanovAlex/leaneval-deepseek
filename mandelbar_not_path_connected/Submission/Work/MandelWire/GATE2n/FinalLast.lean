/-
# GATE2 — the last mile: every non-sibling hypothesis of the case-(ii) drive discharged

`Work.GATE2.twoSided_of_final : Work.GATE.TwoSided c₀ P.Nm` with a hypothesis list consisting of

* the PARIMPL / PARIMPL2 bundles of the root-parabolic parameter (`ParNormal`, `MatchData`,
  `TransitData`, `trans`, the openness/frontier of `P.Nm`, the transit facts, `LockstepAll`),
* the flower `fl` and its flower-fix `FF` with the saturation certificate `hSat`,
* the nest `nest : Z1Nest` and the cylinder lift `Lray`, with its analyticity `han` and the
  side-flip `hflip`,
* the angle identifications `hQa`/`hQb`, the depth `hR`, and the two families of side memberships
  `hPsides`/`hQsides` of the nest landing points (supplied for the assembled nest by
  `Work.GATE2.toZ1Nest_sides` from `Work.GATE2.landing_succ_mem`),
* the tripod data `tr : B2Data` at `b₂` (from which the equator leak `hleak₀` is derived by
  `Work.GATE2.hleak0_of_rigidity`, the contrapositive of `Work.ELRig.rigidity`) —

all of the *derived* data being produced here: the potential bound (`hpot_of_flower`), the
far-left smallness (`ParabolicFlower.Ψ_small`), the level/domain data of the lift
(`hs1_of_rayCylLift`) and the `α₁`-window angle dichotomy (`exists_alpha1_angle_or_shift`).
-/
import Submission.Work.MandelWire.GATE2n.FinalEl
import Submission.Work.GATE2.exists_alpha1_angle_or_shift
import Submission.Work.GATE2.hpot_of_flower
import Submission.Work.GATE2.hs1_of_rayCylLift
import Submission.Work.GATE2.hleak0_of_rigidity

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

/-- **The endgame with all derived data produced internally.** -/
theorem twoSided_of_final {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
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
  twoSided_of_el (d := d) (nIn := nIn) FF trans hOpen hfront hPaeq hφa_eq hΨeq hentry₀ hcrit hSat
    hρc hcont hρh him hblowup hρe hblow hLS hG nest Lray han hflip hQa hQb hR hPsides hQsides
    (fun n x h1 h2 h3 => Work.GATE2.exists_alpha1_angle_or_shift fl nest hQa hQb n h1 h2 h3)
    tr (Work.GATE2.hpot_of_flower (d := d) fl)
    (fun ε hε => (fl.Ψ_small ε hε).imp fun R hR w hw => (hR w hw).2)
    (Work.GATE2.hs1_of_rayCylLift fl nest Lray)

end Work.MandelWire.G2n
