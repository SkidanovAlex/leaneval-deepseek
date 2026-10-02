/-
# GATE2 — the drive with the floored UT taken from PARIMPL2's universal-box lock-step transit

This is the sibling-only form of the headline drive.  It combines the three reductions made in this
round:

* **PL's basin fact** `fl.Pa ⊆ K c₀` is not a hypothesis (`Work.ELRig.Pa_subset_K`);
* **PL's half-plane saturation** is not a hypothesis but the certificate
  `Work.GATE2.SaturatedFlower`, produced by `Work.GATE2.PL.exists_flowerFix_saturating` from the
  single numeric condition at the parabolic point (`Submission/Work/GATE2/Saturating.lean`);
* **the floored UT** `∀ X, Work.GATE2.TransitLockstepAbove … (X+1) …` is not a hypothesis either:
  it is `Work.PARIMPL2.LockstepAll` (PARIMPL2's universal-box form of the design's lock-step
  transit) specialised at the prescribed floor, by `Work.GATE2.utfloorAll_of_lockstepAll`
  (`Submission/Work/GATE2/TransitBridge.lean`).  This is the reviewer item "UT must become a
  PARIMPL field" closed with the sibling export that actually exists.

The transit coordinate is a **parameter** `trans` of the drive (PARIMPL2's `transPh P x₀ θ` in the
intended instantiation), together with the four facts `Work.GATE2.gateTransitData` consumes.

The remaining inputs are therefore: PARIMPL's `ParNormal`/`MatchData`/`TransitData`/`LeakData`, the
flower and its identification, the saturation certificate `hSat`, the real Écalle height `hv`, the
four facts about the transit coordinate, its blow-up `hblow`, PARIMPL2's `LockstepAll`, and the two
exit loops `hEXL₁`, `hEXL₂` at the two leak centres.
-/
import Submission.Work.GATE2.Final
import Submission.Work.GATE2.Saturating
import Submission.Work.GATE2.TransitBridge
import Submission.Work.GATE2.AssemblyPLEXL
import Submission.Work.GATE2.D1.exitPath_of_tongue_trans
import Submission.Work.GATE2.D1.exitPath_of_tongue_iota_trans

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

/-- **The `twoSided` field of `Work.Final.FinalInputs`, from PARIMPL's data, the saturation
certificate, PARIMPL2's lock-step transit and the two exit loops.**  See the module docstring for
the hypothesis list. -/
theorem twoSided_trans_of_lockstepAll {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (trans : ℂ → ℂ)
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hSat : SaturatedFlower fl FF)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) =
        ((((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) + N : ℝ) : ℂ))
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ L.r₀ / 8)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe)
    (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = L.xstar - (L.j₀ : ℝ) ∨ y = L.xstar - (L.j₀ : ℝ) + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < L.r₀ / 2 → c ∉ Mandelbar)
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b)
    (hLS : Work.PARIMPL2.LockstepAll c₀ P.Nm trans M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (hEXL₁ : ExitLoop c₀ fl.Ψ (L.xstar - (L.j₀ : ℝ)) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha1)
    (hEXL₂ : ExitLoop c₀ fl.Ψ ((L.xstar - (L.j₀ : ℝ)) + 1 / 2) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha2) :
    Work.GATE.TwoSided c₀ P.Nm := by
  obtain ⟨hPL⟩ := Work.GATE2.PL.principal_param fl FF (Work.ELRig.Pa_subset_K fl) hSat
    ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) hv
  have hUT := utfloorAll_of_lockstepAll hLS
  refine twoSided_of_trans_exitPath (d := d) (P := P) (M := M) (T := T) (L := L) trans
    hOpen hfront (by rw [hPaeq]; exact fl.isOpen_Pa)
    (by rw [hφa_eq, hPaeq]; exact fl.φa_fatou.1.2.1)
    hentry₀ hcrit hρc hcont hρh hheight hblowup hρe hesc ?_ ?_
  · exact Work.GATE2.D1.exitPath_of_tongue_trans (d := d) (P := P) (M := M) (T := T) (L := L)
      FF trans hPaeq hφa_eq hΨeq hcrit hPL hEXL₁ (hUT hPL.X) hblow
  · exact Work.GATE2.D1.exitPath_of_tongue_iota_trans (d := d) (P := P) (M := M) (T := T) (L := L)
      FF trans hPaeq hφa_eq hΨeq hcrit hPL hEXL₂ (hUT hPL.X) hblow

end Work.GATE2
