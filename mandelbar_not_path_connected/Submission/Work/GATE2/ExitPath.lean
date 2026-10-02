/-
# GATE2 — the exit-path datum and its conversion into the phase residual (the design's D1/D2)

The design `NOTES_LEAD_mandelbar_gate2transport.md` replaces the tube/branch transport of residual 2
by **one dynamical path at a fixed tongue parameter `e`**: a path `σ` from `e` to `F_e e` whose
`(m−1)`-st image under `F_e` stays in the thin `α`-sector and above half the potential of
`z_{m−1} = F_e^{m−1} e`.  The path-transport theorem `Work.GATE2.PathTransport.chainWindow_of_exitPath`
(PT) then gives the whole chain window, and `phaseConj_of_exitPath` gives both conjuncts of
`Work.GATE2.PhaseResidual`.

This module isolates *that* datum as the single residual interface of the area:

* `Work.GATE2.ExitPathData` — the existence, for every parameter of a tongue near `c₀`, of the
  path `σ` with the two estimates;
* `Work.GATE2.phaseResidual_of_exitPath` (**D2**) — `ExitPathData` for the two tongues gives
  `Work.GATE2.PhaseResidual`, hence (through `Work.GATE2.twoSided_of_phaseResidual`) the
  `twoSided` field of `Work.Final.FinalInputs`.

What builds `ExitPathData` itself (the design's D1) is the composition

* **PL** (`Work.GATE2.ExitPathInputs.PrincipalParam`) — the principal Fatou parametrisation
  `ψ : ℂ \ (−∞, v − 1/2] → K c₀` with `ψ v = c₀` and `ψ(w + 1) = F₀ (ψ w)`, built by half-step
  lifts through `g₀ = T^5` and Liouville (`NOTES_LEAD_mandelbar_gate2transport.md` §4.1);
* **EXL** (`Work.GATE2.ExitPathInputs.ExitLoop`) — the `α`-window exit loop at `c₀`, off `K c₀`,
  with potential at least `(3/4)·G(Ψ(u−1))` and the offset-avoidance condition (W) (§4.2, verified
  numerically with large margin by the lead: `lead_mb/gate2_W/`);
* **UT** (`Work.PARIMPL.TransitData.UT`) — PARIMPL's uniform lock-step transit (§5);
* the uniform-continuity bookkeeping of §6 D1 (NAKANE's `continuous_greenFun`,
  `Work.GATE2.deviation_continuousAt`, `Work.PARIMPL.continuous_tsqIter`).

Those three sibling statements are *not* asserted here; they are the residual inputs of the area.
PL and EXL are formalised (as the structures `Work.GATE2.PrincipalParam`, `Work.GATE2.ExitLoop` of
`Submission/Work/GATE2/ExitPathInputs.lean`) and UT is a field of PARIMPL's `TransitData`; the
construction of `ExitPathData` from them (the design's D1) is the one step of this area that is
still owed, and it is recorded as such in `NOTES.md` §5/§9.
-/
import Submission.Work.GATE2.Phase
import Submission.Work.GATE2.PathTransport.chainWindow_of_exitPath
import Submission.Work.GATE2.PathTransport.general.phaseConj_of_exitPath
import Submission.Work.ELRig.cert

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

open LeanEval.ComplexAnalysis (Mandelbar)

/-- **The exit-path datum** (the design's D1 interface): for every parameter `e` of the tongue
`bT` near `c₀` that is off the mandelbar there are `m ≥ 1` and a path `σ` from `e` to `F_e e` along
whose `(m−1)`-st image the `α`-deviation is `< 1/8192` and the Green function exceeds
`1024^(m−1)·G_e(0)`.  By `Work.GATE2.PathTransport.chainWindow_of_exitPath` this datum alone
supplies the whole chain window, and by `Work.GATE2.PathTransport.general.phaseConj_of_exitPath` both conjuncts of the
phase residual. -/
def ExitPathData (c₀ : ℂ) (Nm : Set ℂ) (trans : ℂ → ℂ) (xLeak r₀ : ℝ) (bT : ℂ → Prop)
    (α : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ e ∈ Nm ∩ Metric.ball c₀ ρ, bT e → e ∉ Mandelbar →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ σ : C(unitInterval, ℂ), σ 0 = e ∧ σ 1 = Work.EL.F e e ∧
      (∀ t, |Work.GATE.deviation (Work.Bottcher.varphiCrit e) α
        ((Work.EL.F e)^[m - 1] (σ t))| < (1 / 8192 : ℝ)) ∧
      (∀ t, (1024 : ℝ) ^ (m - 1) * Work.Bottcher.green e 0 <
        Work.Bottcher.green e ((Work.EL.F e)^[m - 1] (σ t)))

/-- The root-angle arithmetic of the design: `1023 α₁ = 371` and `1023 α₂ = 404`. -/
theorem alpha1_mul : 1023 * Work.EL.alpha1 = 371 := by
  rw [Work.ELRig.alpha1_eq]; norm_num [Work.ELRig.qq]

theorem alpha2_mul : 1023 * Work.EL.alpha2 = 404 := by
  rw [Work.ELRig.alpha2_eq]; norm_num [Work.ELRig.qq]

/-- **D2: the phase residual from the exit-path datum of the two tongues.**  This is the whole of
residual 2 (TRANSPORT) once the exit path `σ` is available: for the `b`-tongue the direction is
`α₁`, for the `ι b`-tongue it is `α₂`; in both cases `phaseConj_of_exitPath` produces the phase
identity together with the window bound on the base point `F_e^[m] e`. -/
noncomputable def phaseResidual_of_exitPath {c₀ : ℂ} {Nm : Set ℂ} (TD : Work.GATE.TransitData c₀ Nm)
    (h₁ : ExitPathData c₀ Nm TD.trans TD.xLeak TD.r₀
      (fun e => Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e) Work.EL.alpha1)
    (h₂ : ExitPathData c₀ Nm TD.trans TD.xLeak TD.r₀
      (fun e => Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e) Work.EL.alpha2) :
    PhaseResidual c₀ Nm TD where
  ρ := min (Classical.choose h₁) (Classical.choose h₂)
  hρ := lt_min (Classical.choose_spec h₁).1 (Classical.choose_spec h₂).1
  b := by
    intro e he ht hM
    obtain ⟨m, hm, σ, h0, h1, hdev, hpot⟩ :=
      (Classical.choose_spec h₁).2 e
        ⟨he.1, Metric.ball_subset_ball (min_le_left _ _) he.2⟩ ht hM
    obtain ⟨hwin, hid⟩ := Work.GATE2.PathTransport.general.phaseConj_of_exitPath (e := e)
      ⟨371, alpha1_mul⟩ hm σ h0 h1 hdev hpot
    exact ⟨Work.Bottcher.varphiCrit e, Work.Bottcher.isCritBottcher_varphiCrit e, m, hwin, hid⟩
  iota := by
    intro e he ht hM
    obtain ⟨m, hm, σ, h0, h1, hdev, hpot⟩ :=
      (Classical.choose_spec h₂).2 e
        ⟨he.1, Metric.ball_subset_ball (min_le_right _ _) he.2⟩ ht hM
    obtain ⟨hwin, hid⟩ := Work.GATE2.PathTransport.general.phaseConj_of_exitPath (e := e)
      ⟨404, alpha2_mul⟩ hm σ h0 h1 hdev hpot
    exact ⟨Work.Bottcher.varphiCrit e, Work.Bottcher.isCritBottcher_varphiCrit e, m, hwin, hid⟩

/-- **The `twoSided` field of `Work.Final.FinalInputs` from the exit-path datum.**  Residuals 1
(ACCESS) and 3 (the shifted escape) are not hypotheses: they are proved in this area, and the two
escape fields of GATE's `TransitData` are PARIMPL's own `LeakData.escape`. -/
theorem twoSided_of_exitPath {c₀ : ℂ} {Nm : Set ℂ} (hOpen : IsOpen Nm) (hfront : c₀ ∈ frontier Nm)
    (TD : Work.GATE.TransitData c₀ Nm)
    (h₁ : ExitPathData c₀ Nm TD.trans TD.xLeak TD.r₀
      (fun e => Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e) Work.EL.alpha1)
    (h₂ : ExitPathData c₀ Nm TD.trans TD.xLeak TD.r₀
      (fun e => Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e) Work.EL.alpha2) :
    Work.GATE.TwoSided c₀ Nm :=
  twoSided_of_phaseResidual hOpen hfront TD (phaseResidual_of_exitPath TD h₁ h₂)

end Work.GATE2
