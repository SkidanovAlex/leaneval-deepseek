/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.ExitTracking` — the repaired exit-tracking interfaces of the transit

Two definitions of `Submission/Work/PARIMPL/Transit.lean` were **not** in the form the design
`NOTES_LEAD_mandelbar_gate2transport.md` §2/§5 describes (both defects are reported in
`NOTES_FALSE_ExitTrackedLoc.md` and repaired in the delivered area on 2026-09-28, see
`Submission/Work/PARIMPL/NOTES.md` §0.0).  This file keeps the repaired forms, which are the ones
the sibling inputs of this area use:

* `Work.PARIMPL.ExitTrackedLoc` **was vacuous**: the half-width `Xo` of the window was quantified
  *existentially* with only `0 < ρ` required, so `Xo := 1/2` made the window `[-Xo, -1)` empty and
  the statement held for *arbitrary* `trans`, `Ft`, `Ψ` with no hypotheses.
  `Work.PARIMPL2.ExitTrackedWindow` below is the repaired form (the one GATE2's own
  `Work.GATE2.ExitTrackedLoc` always had): the window width is **universal** (`∀ Xo, 1 < Xo`),
  the tracked quantity is the **integer level** `trans c + (k : ℂ)` of the repelling coordinate,
  and the conclusion is the *approximate* form `‖(Ft c)^[n] c - Ψ (trans c + k)‖ ≤ η` — which is
  exactly what `Work.PARIMPL2.LockstepAll` delivers and what the escape consumes (the escaping
  region is open).  `Work.PARIMPL2.exitTrackedWindow_iff_PARIMPL` /
  `…_iff_GATE2` (`Submission/Work/PARIMPL2/ExitTrackingBridge.lean`) show that after the repair
  the three forms agree.

* `Work.PARIMPL.TransitLockstep` quantifies its box `X₁ ≤ Re φa ≤ X₁ + W` with `X₁` **existential**
  (`∃ X₁ ρ`), whereas the design asks for **every** bounded box.  With `X₁` existential there is no
  way to place the root-orbit chain point `c_N` in the box, and the specialisation to the exit
  tracking (below) cannot be proved.  `Work.PARIMPL2.LockstepAll` is the design's form;
  `transitLockstep_of_lockstepAll` recovers the delivered one, so using the repaired form in the
  inputs weakens nothing.

Everything else about the two interfaces is as in `NOTES_LEAD_mandelbar_gate2transport.md` §5.
-/
import Submission.Work.PARIMPL.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c₀ : ℂ}

/-- **The uniform lock-step transit, in the form of the design**
(`NOTES_LEAD_mandelbar_gate2transport.md` §5): "for every bounded box `X₁ ≤ Re φa ≤ X₁ + W`,
`|Im φa| ≤ H` of the attracting coordinate and every bounded exit window `−Xo ≤ Re u < −1`".

This is `Work.PARIMPL.TransitLockstep` with the box origin `X₁` made **universal**; the delivered
form (`∃ X₁ ρ`) is recovered by `transitLockstep_of_lockstepAll`. -/
def LockstepAll (c₀ : ℂ) (Nm : Set ℂ) (trans : ℂ → ℂ) (nIn : ℕ) (Ft : ℂ → ℂ → ℂ)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) (v : ℝ) : Prop :=
  ∀ H W Xo η X₁ : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧
    ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, ∀ y y' : ℂ, ∀ n : ℕ,
      y ∈ Pa → X₁ ≤ (φa y).re → (φa y).re ≤ X₁ + W → |(φa y).im| ≤ H → ‖y' - y‖ ≤ ρ →
      let u := trans c - nIn - v + n + φa y
      (-Xo) ≤ u.re → u.re < -1 →
        ‖(Ft c)^[n] y' - Ψ u‖ ≤ η

/-- The delivered `Work.PARIMPL.TransitLockstep` follows from the design's form. -/
theorem transitLockstep_of_lockstepAll {Nm : Set ℂ} {trans : ℂ → ℂ} {nIn : ℕ}
    {Ft : ℂ → ℂ → ℂ} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {v : ℝ}
    (h : LockstepAll c₀ Nm trans nIn Ft Pa φa Ψ v) :
    Work.PARIMPL.TransitLockstep c₀ Nm trans nIn Ft Pa φa Ψ v := by
  intro H W Xo η hη
  obtain ⟨ρ, hρ, hρ'⟩ := h H W Xo η 0 hη
  exact ⟨0, ρ, hρ, fun c hc y y' n hy h1 h2 h3 hy' hu1 hu2 =>
    hρ' c hc y y' n hy h1 h2 h3 hy' hu1 hu2⟩

/-- **The repaired bounded-window exit tracking.**  For every window `-X ≤ · < -1` with `1 < X`
and every integer level `trans c + k` of the repelling coordinate of the transit lying in it, a
point of the critical orbit of `c` lies within `η` of `Ψ` of that level.

This replaces the vacuous `Work.PARIMPL.ExitTrackedLoc` (`NOTES_FALSE_ExitTrackedLoc.md`).  Two
points of the form:

* the window width `Xo` is **universal** (`∀ Xo, 1 < Xo`), not existential;
* the tracked quantity is the *critical orbit* against the *level* `trans c + (k : ℂ)`, in the
  **approximate** form `‖(Ft c)^[n] c - Ψ (trans c + k)‖ ≤ η` — the form that the uniform
  lock-step transit delivers directly (`Work.PARIMPL2.exitTrackedWindow_of_lockstep`) and the
  form the escape of `LeakData` consumes (the escaping region is *open*, so an `η`-approximate
  orbit point escapes as well).  The exact-preimage form of `NOTES_LEAD_mandelbar_gate2transport.md`
  §2 (`∃ u, Ψ u = (Ft c)^[n] c ∧ ‖u - (trans c + k)‖ ≤ η`) follows from this one given the local
  inverse of `Ψ` on `Re < -1` (`ParabolicFlower.Ψ_inj`, an ELRig/FatouCoord export). -/
def ExitTrackedWindow (c₀ : ℂ) (Nm : Set ℂ) (trans : ℂ → ℂ) (Ft : ℂ → ℂ → ℂ)
    (Ψ : ℂ → ℂ) : Prop :=
  ∀ Xo : ℝ, 1 < Xo → ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧
    ∀ c ∈ Nm ∩ Metric.ball c₀ ρ, ∀ k : ℤ,
      (-Xo) ≤ (trans c + (k : ℂ)).re → (trans c + (k : ℂ)).re < -1 →
        ∃ n : ℕ, ‖(Ft c)^[n] c - Ψ (trans c + (k : ℂ))‖ ≤ η

end Work.PARIMPL2

end
