/-
# GATE2 — GATE's `TransitData` from a *chosen* leak centre (no `LeakData`)

`Work.GATE2.gateTransitData` (`Submission/Work/GATE2/Relay.lean`) converts PARIMPL's transit data
into GATE's consumer form `Work.GATE.TransitData c₀ P.Nm`.  Of the `LeakData` bundle it uses only
the centre `L.xstar − L.j₀` and the radius `L.r₀`/`L.hr₀`; the escape is a *hypothesis* about the
transit coordinate `trans`, not `L.escape` (because `L.escape` is stated for `transU`, and
`LockstepAll … transU …` is not available — `Submission/Work/PARIMPL2/NOTES_FALSE_*`).

Consequently the whole conversion can be stated with the leak centre as a **free parameter**,
which is what the design's case-(ii) drive needs (`NOTES_LEAD_mandelbar_gaps3.md` §2.2): GATE2
*chooses* the leak centre (the last real point of the lifted equipotential arc) rather than taking
the one pinned by a `LeakData`.

`Work.GATE2.gateTransitDataAt` is the parameterised form; `gateTransitData` is recovered from it by
`xLeak := L.xstar − L.j₀`, `r₀ := L.r₀`, `hr₀ := L.hr₀`.
-/
import Submission.Work.GATE2.Defs
import Submission.Work.PARIMPL.All

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

/-- **GATE's `TransitData` from an arbitrary leak centre `xLeak` and radius `r₀`.**

Signature (the parameterised form of `Work.GATE2.gateTransitData`): the four facts `hρc/hcont`,
`hρh/hheight`, `hblowup`, `hρe/hesc` about the transit coordinate `trans`, the positivity `hr₀`,
and the leak centre `xLeak`; the resulting `TransitData` has
`ρ := min (min (min ρc ρh) ρe) P.ρ₀`, `xLeak := xLeak`, `r₀ := r₀`. -/
noncomputable def gateTransitDataAt {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d}
    (xLeak r₀ : ℝ) (hr₀ : 0 < r₀) (trans : ℂ → ℂ)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ r₀ / 8)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe) (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = xLeak ∨ y = xLeak + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < r₀ / 2 → c ∉ Mandelbar) :
    Work.GATE.TransitData c₀ P.Nm :=
  let ρ : ℝ := min (min (min ρc ρh) ρe) P.ρ₀
  have hρ_ρc : ρ ≤ ρc := le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)
  have hρ_ρh : ρ ≤ ρh := le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _)
  have hρ_ρe : ρ ≤ ρe := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρpos : 0 < ρ := lt_min (lt_min (lt_min hρc hρh) hρe) P.hρ₀
  { xLeak := xLeak
    r₀ := r₀
    hr₀ := hr₀
    ρ := ρ
    hρ := hρpos
    trans := trans
    cont := hcont.mono fun x hx => ⟨hx.1, Metric.ball_subset_ball hρ_ρc hx.2⟩
    height := fun c hc => hheight c ⟨hc.1, Metric.ball_subset_ball hρ_ρh hc.2⟩
    blowup := fun p hp => hblowup p ⟨hp.1, Metric.ball_subset_ball hρ_ρh hp.2⟩
    escape_b := fun c hc hb =>
      hesc c ⟨hc.1, Metric.ball_subset_ball hρ_ρe hc.2⟩ xLeak (Or.inl rfl)
        (distZ_lt_of_bTongue hb)
    escape_iota := fun c hc hb =>
      hesc c ⟨hc.1, Metric.ball_subset_ball hρ_ρe hc.2⟩ (xLeak + 1 / 2) (Or.inr rfl)
        (distZ_lt_of_iotaTongue hb) }

@[simp] theorem gateTransitDataAt_trans {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d}
    (xLeak r₀ : ℝ) (hr₀ : 0 < r₀) (trans : ℂ → ℂ)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ r₀ / 8)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe) (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = xLeak ∨ y = xLeak + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < r₀ / 2 → c ∉ Mandelbar) :
    (gateTransitDataAt (P := P) xLeak r₀ hr₀ trans hρc hcont hρh hheight hblowup hρe hesc).trans
      = trans := rfl

@[simp] theorem gateTransitDataAt_xLeak {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d}
    (xLeak r₀ : ℝ) (hr₀ : 0 < r₀) (trans : ℂ → ℂ)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ r₀ / 8)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe) (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = xLeak ∨ y = xLeak + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < r₀ / 2 → c ∉ Mandelbar) :
    (gateTransitDataAt (P := P) xLeak r₀ hr₀ trans hρc hcont hρh hheight hblowup hρe hesc).xLeak
      = xLeak := rfl

@[simp] theorem gateTransitDataAt_r₀ {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {P : Work.PARIMPL.ParNormal d}
    (xLeak r₀ : ℝ) (hr₀ : 0 < r₀) (trans : ℂ → ℂ)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (hheight : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, |(trans c).im| ≤ r₀ / 8)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe) (hesc : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρe, ∀ y : ℝ,
      (y = xLeak ∨ y = xLeak + 1 / 2) →
      Work.PARIMPL.distZ (trans c) ((y : ℝ) : ℂ) < r₀ / 2 → c ∉ Mandelbar) :
    (gateTransitDataAt (P := P) xLeak r₀ hr₀ trans hρc hcont hρh hheight hblowup hρe hesc).r₀
      = r₀ := rfl

end Work.GATE2
