/-
# GATE2 — the final drive: `twoSided` with PL discharged by `Work.GATE2.PL.principal_param`

> **SUPERSEDED (see `NOTES.md` §20).**  The `Work.GATE2.twoSided` of this file asks for
> `PARIMPL.LeakData`, `hK`, `hHalf`, `hv`, the universally floored UT and the two `ExitLoop`s.
> The current deliverable of the area, with a hypothesis list consisting only of sibling exports,
> is `Work.GATE2.twoSided_of_exports` / `Work.GATE2.twoSided_of_final`
> (`Submission/Work/GATE2/FinalCaseII.lean`, `Submission/Work/GATE2/FinalLast.lean`).  This file is
> kept because the D1/PL/EXL route it exposes is still the interface of those sub-areas.

`Work.GATE2.twoSided_of_PARIMPL_PL_EXL` (`Submission/Work/GATE2/AssemblyPLEXL.lean`) reduces
`Work.GATE.TwoSided c₀ P.Nm` to PL (`PrincipalParam`), EXL (`ExitLoop` at the two leak centres) and
the floored UT, on top of PARIMPL's data and the flower facts.  This module discharges **PL** using
the delivered `Work.GATE2.PL.principal_param`: the parametrisation exists as soon as

* `fl.Pa ⊆ K c₀` (the basin fact of the `c₀`-flower; `Work.ELRig.Pa_subset_K`);
* the attracting Fatou coordinate saturates a right half-plane of the invariant sub-petal
  (`hHalf`, the maximal-petal statement of `FatouCoordFix`);
* the real Écalle height of the entry point matches the critical orbit
  (`hv`, from `hcrit` and `MatchData.entering`).

The result is a theorem whose hypotheses are PARIMPL's data, the flower facts, `hK`, `hHalf`, `hv`,
UT (with the universal floor), and **EXL** — the only remaining construction, supplied by
`Work.GATE2.EXL.exitLoop_of_rayLift` / `…_iota` from the ray-lift access of residual 1
(`Work.ELRig.RayCylLift`) plus the no-overshoot condition of the design.
-/
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.Relay
import Submission.Work.GATE2.Bridge
import Submission.Work.GATE2.AssemblyPLEXL
import Submission.Work.GATE2.PL.principal_param
import Submission.Work.GATE2.EXL.OfSegment
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

/-- **The `twoSided` field of `Work.Final.FinalInputs`, with PL discharged.**  The hypotheses are
PARIMPL's `ParNormal`/`MatchData`/`TransitData`/`LeakData`, the flower facts, the three PL inputs
(`hK`, `hHalf`, `hv`), UT with the universal floor `∀ X`, and EXL at the two leak centres.
Residuals 1 and 3 are not hypotheses. -/
theorem twoSided {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hK : fl.Pa ⊆ Work.EL.K c₀)
    (hHalf : ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) =
        ((((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) + N : ℝ) : ℂ))
    (hUT : ∀ X : ℝ, TransitLockstepAbove c₀ P.Nm (Work.PARIMPL.transU P M.nIn) M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ (X + 1)
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (hEXL₁ : ExitLoop c₀ fl.Ψ (L.xstar - (L.j₀ : ℝ)) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha1)
    (hEXL₂ : ExitLoop c₀ fl.Ψ ((L.xstar - (L.j₀ : ℝ)) + 1 / 2) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha2) :
    Work.GATE.TwoSided c₀ P.Nm := by
  obtain ⟨hPL⟩ := Work.GATE2.PL.principal_param fl FF hK hHalf
    ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) hv
  exact twoSided_of_PARIMPL_PL_EXL FF hOpen hfront hPaeq hφa_eq hΨeq hentry₀ hcrit
    hPL hEXL₁ hEXL₂ (hUT hPL.X)

/-- **The `twoSided` field of `Work.Final.FinalInputs` from PARIMPL's bundled input.**  This is the
sharpest sibling-only form: the *only* hypotheses beyond PARIMPL's `ParImplInputs H` (which bundles
`ParNormal`/`MatchData`/`TransitData`/`LeakData`, the `FatouCoord` fix, the openness of the petal,
the entry point, the vanishing critical height, the openness of the implosion side and its
accumulation at `c₀` — see `Work.PARIMPL.ParImplInputs.isOpen_Nm`, `…mem_frontier_Nm`) are

* the flower `fl` (the ELRig construction) and its identification with PARIMPL's coordinates
  (`hPaeq`, `hφa_eq`, `hΨeq` — satisfied by *definition* when `ParImplInputs` is instantiated at
  `Pa := fl.Pa`, `φa := fl.φa`, `Ψ := fl.Ψ`);
* PL's three inputs `hK`, `hHalf`, `hv`;
* UT with the universal floor, `hUT : ∀ X` (the strengthening PARIMPL must export beside `UT`);
* EXL at the two leak centres, `hEXL₁`, `hEXL₂` — supplied by
  `Work.GATE2.EXL.exitLoop_of_rayLift` / `…_iota` from the ray-lift access.

Residuals 1 (ACCESS) and 3 (the shifted escape) are not hypotheses. -/
theorem twoSided_of_ParImplInputs (H : Work.PARIMPL.ParImplInputs)
    {fl : Work.EL.ParabolicFlower (Work.EL.F H.c₀) ((Tantibar H.c₀)^[5]) H.d.z₁}
    (hPaeq : H.Pa = fl.Pa) (hφa_eq : H.φa = fl.φa) (hΨeq : H.Ψ = fl.Ψ)
    (hK : fl.Pa ⊆ Work.EL.K H.c₀)
    (hHalf : ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ H.fix.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F H.c₀)^[N] H.c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F H.c₀)^[N] H.c₀) =
        ((((H.φa (Work.PARIMPL.entryPt H.P H.M.nIn H.c₀)).re - (H.M.nIn : ℝ)) + N : ℝ) : ℂ))
    (hUT : ∀ X : ℝ, TransitLockstepAbove H.c₀ H.P.Nm (Work.PARIMPL.transU H.P H.M.nIn) H.M.nIn
      (fun c z => Work.PARIMPL.Ft c z) H.Pa H.φa H.Ψ (X + 1)
      ((H.φa (Work.PARIMPL.entryPt H.P H.M.nIn H.c₀)).re - (H.M.nIn : ℝ)))
    (hEXL₁ : ExitLoop H.c₀ fl.Ψ (H.L.xstar - (H.L.j₀ : ℝ)) H.L.r₀
      ((H.φa (Work.PARIMPL.entryPt H.P H.M.nIn H.c₀)).re - (H.M.nIn : ℝ)) Work.EL.alpha1)
    (hEXL₂ : ExitLoop H.c₀ fl.Ψ ((H.L.xstar - (H.L.j₀ : ℝ)) + 1 / 2) H.L.r₀
      ((H.φa (Work.PARIMPL.entryPt H.P H.M.nIn H.c₀)).re - (H.M.nIn : ℝ)) Work.EL.alpha2) :
    Work.GATE.TwoSided H.c₀ H.P.Nm := by
  set FF : Work.PARIMPL.FlowerFix H.d (Work.EL.F H.c₀) ((Tantibar H.c₀)^[5]) H.d.z₁ fl.Pa fl.φa :=
    { shift := fun z hz => by rw [← hφa_eq]; exact H.fix.shift z (hPaeq.symm ▸ hz)
      Pg := H.fix.Pg
      Pg_sub := fun z hz => hPaeq ▸ H.fix.Pg_sub hz
      isOpen_Pg := H.fix.isOpen_Pg
      mapsTo_F_Pg := H.fix.mapsTo_F_Pg
      mapsTo_G_Pg := H.fix.mapsTo_G_Pg } with hFFdef
  exact twoSided (d := H.d) (fl := fl) FF H.isOpen_Nm H.mem_frontier_Nm hPaeq hφa_eq hΨeq
    H.entry_mem H.critHeight_zero hK hHalf hv hUT hEXL₁ hEXL₂

/-- **The `twoSided` field of `Work.Final.FinalInputs` with the EXL slots fed by the *real-segment*
data.**  The two hypotheses `h₁`, `h₂` are the output of
`Work.GATE2.EXL.exitLoop_of_deepSegment_all` — the exit loop for every radius below `R` and every
height, at the two leak centres — which in turn follows from the one-dimensional data on the real
segments `[y₀−2, y₀+1]` and `[y₀−1/2, y₀+3/2]` (`hdev`: the `α`-deviation, `hoffK`: avoidance of
`K c₀`, `hgr`: the oscillation bound on `ρ` of `EXL/Defs.lean`).  The extra conjunct `L.r₀ ≤ R` is
PARIMPL's free choice of the leak radius (their `LeakData` docstring: "the radius `r₀` remains
free").

Every hypothesis is therefore either PARIMPL's own data, a flower fact, one of PL's three inputs,
the floored UT, or the *one-dimensional* leak-segment data — no `ExitLoop` is assumed. -/
theorem twoSided_of_segment {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hK : fl.Pa ⊆ Work.EL.K c₀)
    (hHalf : ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) =
        ((((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) + N : ℝ) : ℂ))
    (hUT : ∀ X : ℝ, TransitLockstepAbove c₀ P.Nm (Work.PARIMPL.transU P M.nIn) M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ (X + 1)
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (h₁ : ∃ R : ℝ, 0 < R ∧ L.r₀ ≤ R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
      Nonempty (ExitLoop c₀ fl.Ψ (L.xstar - (L.j₀ : ℝ)) r₀ v Work.EL.alpha1))
    (h₂ : ∃ R : ℝ, 0 < R ∧ L.r₀ ≤ R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
      Nonempty (ExitLoop c₀ fl.Ψ ((L.xstar - (L.j₀ : ℝ)) + 1 / 2) r₀ v Work.EL.alpha2)) :
    Work.GATE.TwoSided c₀ P.Nm := by
  obtain ⟨R₁, -, hfit₁, hgen₁⟩ := h₁
  obtain ⟨R₂, -, hfit₂, hgen₂⟩ := h₂
  refine twoSided (T := T) (L := L) FF hOpen hfront hPaeq hφa_eq hΨeq hentry₀ hcrit hK hHalf hv hUT ?_ ?_
  · exact Classical.choice (hgen₁ L.r₀ ⟨L.hr₀, hfit₁⟩ _)
  · exact Classical.choice (hgen₂ L.r₀ ⟨L.hr₀, hfit₂⟩ _)

/-- **`Work.GATE2.twoSided_trans` — the deliverable with the transit coordinate as a PARAMETER.**

The lead's instruction (`NOTES_LEAD_mandelbar_implosion.md` §2/§5): PARIMPL's `transU` carries a
non-vanishing phase error, and PARIMPL2 replaces it by the real phase
`transPh c = Re φa(z_e) + θ − π/λ_c`.  This is the analogue of `Work.GATE2.twoSided` in which the
transit coordinate is an explicit argument `trans : ℂ → ℂ`, together with

* the four facts `Work.GATE2.gateTransitData` consumes (`hcont`, `hheight`, `hblowup`, `hesc`; see
  `Relay.lean` for the exact signature PARIMPL2 must match), and
* the blow-up at `c₀` (`hblow`, the form `PL.bTongue_exitTime` uses; it follows from `hblowup` and
  `hfront` since `c₀ ∈ frontier P.Nm ∩ ball c₀ ρh`).

Everything else is as in `Work.GATE2.twoSided`: PL is discharged by
`Work.GATE2.PL.principal_param`, and the exit path is built by the `trans`-generic D1s. -/
theorem twoSided_trans {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (trans : ℂ → ℂ)
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hK : fl.Pa ⊆ Work.EL.K c₀)
    (hHalf : ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
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
    (hUT : ∀ X : ℝ, TransitLockstepAbove c₀ P.Nm trans M.nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ (X + 1)
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)))
    (hEXL₁ : ExitLoop c₀ fl.Ψ (L.xstar - (L.j₀ : ℝ)) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha1)
    (hEXL₂ : ExitLoop c₀ fl.Ψ ((L.xstar - (L.j₀ : ℝ)) + 1 / 2) L.r₀
      ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) Work.EL.alpha2) :
    Work.GATE.TwoSided c₀ P.Nm := by
  obtain ⟨hPL⟩ := Work.GATE2.PL.principal_param fl FF hK hHalf
    ((φa (Work.PARIMPL.entryPt P M.nIn c₀)).re - (M.nIn : ℝ)) hv
  refine twoSided_of_trans_exitPath (d := d) (P := P) (M := M) (T := T) (L := L) trans
    hOpen hfront hPa hφa hentry₀ hcrit hρc hcont hρh hheight hblowup hρe hesc ?_ ?_
  · exact Work.GATE2.D1.exitPath_of_tongue_trans (d := d) (P := P) (M := M) (T := T) (L := L)
      FF trans hPaeq hφa_eq hΨeq hcrit hPL hEXL₁ (hUT hPL.X) hblow
  · exact Work.GATE2.D1.exitPath_of_tongue_iota_trans (d := d) (P := P) (M := M) (T := T) (L := L)
      FF trans hPaeq hφa_eq hΨeq hcrit hPL hEXL₂ (hUT hPL.X) hblow

end Work.GATE2
