/-
# GATE2 — RELAY: PARIMPL's data as GATE's `TransitData`

The GATE chapter consumes the *consumer form* `Work.GATE.TransitData c₀ Nm` of the transit of the
imploded parabolic germ.  Its provenance is PARIMPL's `ParNormal`/`MatchData`/`TransitData`/
`LeakData`; the conversion is pure bookkeeping of radii and of the two leak lattices, and it is the
job of the bridge module `Submission/Work/GATE/Bridge/transitData_fields_of_PARIMPL.lean`.

That module is written against an older PARIMPL interface (`MatchData` with a third argument) and
is currently stale, so GATE2 carries its own copy of the conversion here — against the interface
that is actually on disk.  This also *shrinks* the hypothesis list of the final drive: the escape
fields of GATE's `TransitData` are taken from PARIMPL's own `LeakData.escape` field, which is
stated for the two lattices `x* − j₀ + ℤ` and `x* − j₀ + 1/2 + ℤ` (i.e. it *is* the shifted
`trans_escape`), so no GATE2-specific escape hypothesis remains.

## The conversion

* `trans := transU P M.nIn`, `xLeak := L.xstar − L.j₀`, `r₀ := L.r₀`;
* the neighbourhood radius is `min (min (min ρ_h ρ_e) T.ρ₁) P.ρ₀`, where `ρ_h` comes from
  `TransitData.height` at the level `L.r₀/8` and `ρ_e` from `LeakData.escape`; the term `T.ρ₁`
  keeps the continuity statement (`TransitData.cont` lives on `ball c₀ T.ρ₁`) and `P.ρ₀` keeps the
  blow-up points inside the normal-form ball;
* `bTongue`/`iotaTongue` are converted to `distZ` by `Work.GATE2.distZ_lt_of_bTongue` /
  `..._of_iotaTongue`, the form `LeakData.escape` consumes.

## Main results

* `Work.GATE2.transitData_of_PARIMPL` — `Nonempty (Work.GATE.TransitData c₀ P.Nm)`.
-/
import Submission.Work.GATE2.Defs
import Submission.Work.PARIMPL.Match
import Submission.Work.PARIMPL.Transit
import Submission.Work.PARIMPL.Leak

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

/-- **GATE's `TransitData` from a *given* transit coordinate `trans : ℂ → ℂ`.**

**The transit coordinate is a PARAMETER.**  PARIMPL's `transU P M.nIn` is only the *current*
candidate: `NOTES_LEAD_mandelbar_implosion.md` §2/§5 records that it carries a non-vanishing phase
error, and PARIMPL2 is replacing it by the real phase `transPh c = Re φa(z_e) + θ − π/λ_c`
(exported as `LavaursPhase`).  This definition therefore takes `trans` and the four facts about it
that GATE's `TransitData` needs, so that the caller instantiates `trans := transPh` later; the
instance at `transU` is `Work.GATE2.transitData_of_PARIMPL` below.

**The exact signature PARIMPL2 must match** (coordinate this with them):

```
gateTransitData (trans : ℂ → ℂ)
  (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
  (hρh : 0 < ρh) (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ L.r₀ / 8)
  (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
  (hρe : 0 < ρe) (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = L.xstar − L.j₀ ∨ y = L.xstar − L.j₀ + 1/2) →
      distZ (trans c) (y : ℂ) < L.r₀ / 2 → c ∉ Mandelbar)
    : Work.GATE.TransitData c₀ P.Nm
```

The resulting `TransitData` has `ρ := min (min (min ρc ρh) ρe) P.ρ₀`, `xLeak := L.xstar − L.j₀`,
`r₀ := L.r₀`. -/
noncomputable def gateTransitData {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (trans : ℂ → ℂ)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh) (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ L.r₀ / 8)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe) (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = L.xstar - (L.j₀ : ℝ) ∨ y = L.xstar - (L.j₀ : ℝ) + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < L.r₀ / 2 → c ∉ Mandelbar) :
    Work.GATE.TransitData c₀ P.Nm :=
  let ρ : ℝ := min (min (min ρc ρh) ρe) P.ρ₀
  have hρ_ρc : ρ ≤ ρc := le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)
  have hρ_ρh : ρ ≤ ρh := le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _)
  have hρ_ρe : ρ ≤ ρe := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρpos : 0 < ρ := lt_min (lt_min (lt_min hρc hρh) hρe) P.hρ₀
  { xLeak := L.xstar - (L.j₀ : ℝ)
    r₀ := L.r₀
    hr₀ := L.hr₀
    ρ := ρ
    hρ := hρpos
    trans := trans
    cont := hcont.mono fun x hx => ⟨hx.1, Metric.ball_subset_ball hρ_ρc hx.2⟩
    height := fun c hc => hheight c ⟨hc.1, Metric.ball_subset_ball hρ_ρh hc.2⟩
    blowup := fun p hp => hblowup p ⟨hp.1, Metric.ball_subset_ball hρ_ρh hp.2⟩
    escape_b := fun c hc hb =>
      hesc c ⟨hc.1, Metric.ball_subset_ball hρ_ρe hc.2⟩ (L.xstar - (L.j₀ : ℝ)) (Or.inl rfl)
        (distZ_lt_of_bTongue hb)
    escape_iota := fun c hc hb =>
      hesc c ⟨hc.1, Metric.ball_subset_ball hρ_ρe hc.2⟩ (L.xstar - (L.j₀ : ℝ) + 1 / 2)
        (Or.inr rfl) (distZ_lt_of_iotaTongue hb) }

@[simp] theorem gateTransitData_trans_gen {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (trans : ℂ → ℂ)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh) (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ L.r₀ / 8)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe) (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = L.xstar - (L.j₀ : ℝ) ∨ y = L.xstar - (L.j₀ : ℝ) + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < L.r₀ / 2 → c ∉ Mandelbar) :
    (gateTransitData (d := d) (P := P) (M := M) (T := T) (L := L) trans hρc hcont hρh hheight
      hblowup hρe hesc).trans = trans := rfl

noncomputable def gateTransitData_transU {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0) :
    Work.GATE.TransitData c₀ P.Nm :=
  let ρH := Classical.choose
    (T.height hPa hφa hentry₀ hcrit (L.r₀ / 8) (by linarith [L.hr₀]))
  let hρH := (Classical.choose_spec
    (T.height hPa hφa hentry₀ hcrit (L.r₀ / 8) (by linarith [L.hr₀]))).1
  let hρHle := (Classical.choose_spec
    (T.height hPa hφa hentry₀ hcrit (L.r₀ / 8) (by linarith [L.hr₀]))).2.1
  let hheightH := (Classical.choose_spec
    (T.height hPa hφa hentry₀ hcrit (L.r₀ / 8) (by linarith [L.hr₀]))).2.2
  let ρE := Classical.choose L.escape
  let hρE := (Classical.choose_spec L.escape).1
  let hescE := (Classical.choose_spec L.escape).2
  have hblow : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρH,
      Tendsto (fun c => (Work.PARIMPL.transU P M.nIn c).re) (𝓝[P.Nm] p) atBot := fun p hp => by
    have hball₁ : p ∈ Metric.ball c₀ T.ρ₁ := Metric.ball_subset_ball hρHle hp.2
    have hball₀ : p ∈ Metric.ball c₀ P.ρ₀ := Metric.ball_subset_ball T.le_ρ₀ hball₁
    have hp' := hp.1
    rw [frontier_eq_closure_inter_closure] at hp'
    have hnot : p ∉ P.Nm := by
      intro hmem
      have hn : P.Nm ∈ 𝓝 p := P.isOpen_Nm.mem_nhds hmem
      obtain ⟨y, hyn, hyc⟩ := (mem_closure_iff_nhds.mp hp'.2) P.Nm hn
      exact hyc hyn
    exact T.blowup p (P.a2_zero_of_closure_notMem hp'.1 hball₀ hnot) hball₀
  gateTransitData (d := d) (P := P) (M := M) (T := T) (L := L)
    (fun c => Work.PARIMPL.transU P M.nIn c)
    T.hρ₁ T.cont hρH hheightH hblow hρE hescE

@[simp] theorem gateTransitData_trans {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0) :
    (gateTransitData_transU hPa hφa hentry₀ hcrit (d := d) (P := P) (M := M) (T := T) (L := L)).trans =
      fun c => Work.PARIMPL.transU P M.nIn c := rfl

@[simp] theorem gateTransitData_xLeak {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0) :
    (gateTransitData_transU hPa hφa hentry₀ hcrit (d := d) (P := P) (M := M) (T := T) (L := L)).xLeak =
      L.xstar - (L.j₀ : ℝ) := rfl

@[simp] theorem gateTransitData_r₀ {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0) :
    (gateTransitData_transU hPa hφa hentry₀ hcrit (d := d) (P := P) (M := M) (T := T) (L := L)).r₀ =
      L.r₀ := rfl

/-- **GATE's `TransitData` from PARIMPL's transit and leak data.**  The transit coordinate is
`transU P M.nIn`, its continuity, its height bound at the leak radius `L.r₀/8` and its phase
blow-up on the whole frontier of `Nm` are PARIMPL's own (`TransitData.cont`, `TransitData.height`,
`TransitData.blowup`); the two escape fields are PARIMPL's `LeakData.escape` field, which is
stated for exactly the two lattices `L.xstar − L.j₀ + ℤ` and `L.xstar − L.j₀ + 1/2 + ℤ` of GATE's
two tongues. -/
theorem transitData_of_PARIMPL {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    {M : Work.PARIMPL.MatchData d P Pa φa Ψ}
    {T : Work.PARIMPL.TransitData d P Pa φa Ψ M}
    {L : Work.PARIMPL.LeakData d P Pa φa Ψ M T}
    (hPa : IsOpen Pa) (hφa : DifferentiableOn ℂ φa Pa)
    (hentry₀ : Work.PARIMPL.entryPt P M.nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P M.nIn c₀)).im = 0) :
    Nonempty (Work.GATE.TransitData c₀ P.Nm) :=
  ⟨gateTransitData_transU (d := d) (P := P) (M := M) (T := T) (L := L) hPa hφa hentry₀ hcrit⟩

end Work.GATE2
