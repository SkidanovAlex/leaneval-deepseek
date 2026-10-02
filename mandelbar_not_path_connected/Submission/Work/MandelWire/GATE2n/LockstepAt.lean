/-
# GATE2 — the drive with the leak centre **chosen by GATE2** (design §2.2 of gaps3)

* `Work.GATE2.twoSided_of_trans_exitPathAt` (`BridgeAt.lean`): the drive from an arbitrary leak
  centre, with no `LeakData`.
* **`Work.GATE2.twoSided_trans_of_lockstepAllAt`**: the same drive with everything but the two
  exit loops discharged.  Its hypothesis list is

  1. PARIMPL's `ParNormal`/`MatchData`/`TransitData` (`P`, `M`, `T`);
  2. the flower `fl` and the `FatouCoord` fix `FF` (with `Pa = fl.Pa`, `φa = fl.φa`, `Ψ = fl.Ψ`),
     the entry facts `hentry₀`, `hcrit`, and the saturation certificate `hSat` (a theorem from the
     numeric condition `Re ((2/3)F'''/F''²) < 1` at the parabolic point);
  3. the transits facts (`hcont`, `him`/`hheight`, `hblowup`, `hblow`) and PARIMPL2's
     `LockstepAll` (the uniform lock-step transit);
  4. the leak centre `xLeak`, the radius `r₀ > 0` and the **escape** `hesc` for that centre;
  5. the two exit loops `hEXL₁`, `hEXL₂` at `xLeak` and `xLeak + 1/2`.

  `hv` (the real Écalle height of the entry point) is **not** a hypothesis: it is
  `Work.GATE2.hv_of_crit`, from `hentry₀`, `hcrit` and the identifications (`Hv.lean`).
-/
import Submission.Work.GATE2.Lockstep
import Submission.Work.GATE2.BridgeAt
import Submission.Work.MandelWire.GATE2n.Hv
import Submission.Work.MandelWire.GATE2n.IotaFree

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

namespace Work.MandelWire.G2n

open Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The `twoSided` field of `Work.Final.FinalInputs`, with the leak centre chosen by GATE2.** -/
theorem twoSided_trans_of_lockstepAllAt {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    (nIn : ℕ)
    (xLeak r₀ : ℝ) (hr₀ : 0 < r₀) (trans : ℂ → ℂ)
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P nIn c₀)).im = 0)
    (hSat : SaturatedFlower fl FF)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ r₀ / 8)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe)
    (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = xLeak ∨ y = xLeak + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < r₀ / 2 → c ∉ Mandelbar)
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b)
    (hLS : Work.PARIMPL2.LockstepAll c₀ P.Nm trans nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ
      ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)))
    (hEXL₁ : ExitLoop c₀ fl.Ψ xLeak r₀
      ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)) Work.EL.alpha1)
    (hEXL₂ : ExitLoop c₀ fl.Ψ (xLeak + 1 / 2) r₀
      ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)) Work.EL.alpha2) :
    Work.GATE.TwoSided c₀ P.Nm := by
  obtain ⟨hPL⟩ := Work.GATE2.PL.principal_param fl FF (Work.ELRig.Pa_subset_K fl) hSat
    ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ))
    (hv_of_crit (d := d) (fl := fl) (P := P) (nIn := nIn) hPaeq hφa_eq hentry₀ hcrit)
  have hUT := utfloorAll_of_lockstepAll hLS
  refine twoSided_of_trans_exitPathAt (d := d) (P := P) hOpen hfront xLeak r₀ hr₀ trans
    hρc hcont hρh hheight hblowup hρe hesc ?_ ?_
  · exact Work.MandelWire.G2n.exitPath_of_tongue_trans (nIn := nIn) FF xLeak r₀ hr₀ trans
      hPaeq hφa_eq hΨeq hcrit hPL hEXL₁ (hUT hPL.X) hblow
  · exact Work.MandelWire.G2n.exitPath_of_tongue_iota_trans (nIn := nIn) FF xLeak r₀ hr₀ trans
      hPaeq hφa_eq hΨeq hcrit hPL hEXL₂ (hUT hPL.X) hblow

end Work.MandelWire.G2n
