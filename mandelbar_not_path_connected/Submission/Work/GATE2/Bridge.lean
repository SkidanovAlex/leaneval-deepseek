/-
# GATE2 — the drive: `twoSided` from PARIMPL's data and the exit-path datum of residual 2

This module is the endgame wiring of the GATE chain in PARIMPL's own vocabulary.  It

* builds GATE's `Work.GATE.TransitData c₀ P.Nm` from PARIMPL's `ParNormal`/`MatchData`/
  `TransitData`/`LeakData` through `Work.GATE2.gateTransitData` (module
  `Submission/Work/GATE2/Relay.lean`, the refresh of the stale `Work.GATE.Bridge.transitData_of_PARIMPL`
  against the interface on disk).  Both escape fields of GATE's `TransitData` come from PARIMPL's
  *own* `LeakData.escape` field, which is stated for the two leak lattices `x* − j₀ + ℤ` and
  `x* − j₀ + 1/2 + ℤ` — i.e. the shifted `trans_escape` of residual 3 is no longer a hypothesis;
* feeds residual 2 in its sharpest form — the *exit-path datum* `Work.GATE2.ExitPathData` of the
  two tongues (`Submission/Work/GATE2/ExitPath.lean`, the design's D1 interface) — into
  `Work.GATE2.twoSided_of_exitPath`.

## The hypothesis list of the drive

Beyond PARIMPL's own data (`ParNormal`, `MatchData`, `TransitData`, `LeakData` — with `UT` a
*field* of `TransitData`), the hypotheses are

* `hOpen`, `hfront` — the elementary structure of the implosion side `P.Nm`;
* `hPa`, `hφa`, `hentry₀`, `hcrit` — the flower facts consumed by PARIMPL's `TransitData.height`;
* `h₁`, `h₂` — the exit-path datum `ExitPathData` for the `b`-tongue (`α₁`) and the `ι b`-tongue
  (`α₂`), i.e. the design's D1: for every tongue parameter near `c₀` a path `σ` from `e` to `F_e e`
  whose `(m−1)`-st image stays in the thin `α`-sector and above half the potential.

Residual 1 (ACCESS, `Submission/Work/GATE2/Access.lean`) and residual 3 (the shifted escape) are
*proved* in this area; residual 2 is reduced to `ExitPathData` by PT + the local phase lemma, and
`ExitPathData` itself is what PL + EXL + UT supply (see `NOTES.md` §0 and
`Submission/Work/GATE2/ExitPath.lean`).
-/
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.Relay

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

/-- **The `twoSided` field of `Work.Final.FinalInputs` in PARIMPL's vocabulary, from the exit-path
datum.**  The single residual beyond PARIMPL's data and the four flower facts is `ExitPathData`
for the two tongues — the design's D1. -/
theorem twoSided_of_PARIMPL_exitPath {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (h₁ : ExitPathData c₀ P.Nm (fun c => Work.PARIMPL.transU P M.nIn c)
      (L.xstar - (L.j₀ : ℝ)) L.r₀
      (fun e => Work.GATE.bTongue (fun c => Work.PARIMPL.transU P M.nIn c)
        (L.xstar - (L.j₀ : ℝ)) L.r₀ e) Work.EL.alpha1)
    (h₂ : ExitPathData c₀ P.Nm (fun c => Work.PARIMPL.transU P M.nIn c)
      (L.xstar - (L.j₀ : ℝ)) L.r₀
      (fun e => Work.GATE.iotaTongue (fun c => Work.PARIMPL.transU P M.nIn c)
        (L.xstar - (L.j₀ : ℝ)) L.r₀ e) Work.EL.alpha2) :
    Work.GATE.TwoSided c₀ P.Nm :=
  twoSided_of_exitPath hOpen hfront (gateTransitData_transU hPa hφa hentry₀ hcrit) h₁ h₂

/-- **The same drive with the residual stated as the phase identity of §2.3** (the two conjuncts of
`Work.GATE2.PhaseResidual`), in the sibling-blind vocabulary: for a tongue parameter `e` off the
mandelbar there are a critical Böttcher coordinate `φ`, a number `m` of gate steps and both the
window bound `|deviation φ α (F_e^[m] e)| < windowEps` and the phase identity

`deviation φ α e = deviation φ α (F_e^[m] e) / 1024^m`.

This is *strictly* the statement `Work.GATE2.phaseResidual_of_exitPath` converts from the
exit-path datum, so it is the form in which a caller who has PL + EXL + UT (but not the bookkeeping
of `ExitPathData`) can feed the drive. -/
theorem twoSided_of_PARIMPL_phase {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hP₁ : ∃ ρ > 0, ∀ e ∈ P.Nm ∩ Metric.ball c₀ ρ,
      Work.GATE.bTongue (fun c => Work.PARIMPL.transU P M.nIn c) (L.xstar - (L.j₀ : ℝ)) L.r₀ e →
        e ∉ Mandelbar → ∃ φ : ℂ → ℂ, Work.ParamRays.IsCritBottcher e φ ∧ ∃ m : ℕ,
          |Work.GATE.deviation φ Work.EL.alpha1 ((Work.EL.F e)^[m] e)| < Work.Final.windowEps ∧
          Work.GATE.deviation φ Work.EL.alpha1 e =
            Work.GATE.deviation φ Work.EL.alpha1 ((Work.EL.F e)^[m] e) / (1024 : ℝ) ^ m)
    (hP₂ : ∃ ρ > 0, ∀ e ∈ P.Nm ∩ Metric.ball c₀ ρ,
      Work.GATE.iotaTongue (fun c => Work.PARIMPL.transU P M.nIn c) (L.xstar - (L.j₀ : ℝ)) L.r₀ e →
        e ∉ Mandelbar → ∃ φ : ℂ → ℂ, Work.ParamRays.IsCritBottcher e φ ∧ ∃ m : ℕ,
          |Work.GATE.deviation φ Work.EL.alpha2 ((Work.EL.F e)^[m] e)| < Work.Final.windowEps ∧
          Work.GATE.deviation φ Work.EL.alpha2 e =
            Work.GATE.deviation φ Work.EL.alpha2 ((Work.EL.F e)^[m] e) / (1024 : ℝ) ^ m) :
    Work.GATE.TwoSided c₀ P.Nm := by
  obtain ⟨ρ₁, hρ₁, hb⟩ := hP₁
  obtain ⟨ρ₂, hρ₂, hi⟩ := hP₂
  refine twoSided_of_phaseResidual hOpen hfront
    (gateTransitData_transU (d := d) (P := P) (M := M) (T := T) (L := L) hPa hφa hentry₀ hcrit)
    ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_, ?_⟩
  · intro e he ht hM
    exact hb e ⟨he.1, Metric.ball_subset_ball (min_le_left _ _) he.2⟩ ht hM
  · intro e he ht hM
    exact hi e ⟨he.1, Metric.ball_subset_ball (min_le_right _ _) he.2⟩ ht hM

/-- **The drive with the transit coordinate as a PARAMETER.**  PARIMPL's `transU` is only the
current candidate (`NOTES_LEAD_mandelbar_implosion.md` §2/§5: it carries a non-vanishing phase
error); PARIMPL2 replaces it by the real phase `transPh c = Re φa(z_e) + θ − π/λ_c`.  This is the
form of the drive that the replacement instantiates: the four facts about `trans` are exactly the
signature of `Work.GATE2.gateTransitData` (see `Relay.lean`). -/
theorem twoSided_of_trans_exitPath {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (trans : ℂ → ℂ)
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ L.r₀ / 8)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe)
    (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = L.xstar - (L.j₀ : ℝ) ∨ y = L.xstar - (L.j₀ : ℝ) + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < L.r₀ / 2 → c ∉ Mandelbar)
    (h₁ : ExitPathData c₀ P.Nm trans (L.xstar - (L.j₀ : ℝ)) L.r₀
      (fun e => Work.GATE.bTongue trans (L.xstar - (L.j₀ : ℝ)) L.r₀ e) Work.EL.alpha1)
    (h₂ : ExitPathData c₀ P.Nm trans (L.xstar - (L.j₀ : ℝ)) L.r₀
      (fun e => Work.GATE.iotaTongue trans (L.xstar - (L.j₀ : ℝ)) L.r₀ e) Work.EL.alpha2) :
    Work.GATE.TwoSided c₀ P.Nm :=
  twoSided_of_exitPath hOpen hfront
    (gateTransitData (d := d) (P := P) (M := M) (T := T) (L := L) trans
      hρc hcont hρh hheight hblowup hρe hesc) h₁ h₂

end Work.GATE2
