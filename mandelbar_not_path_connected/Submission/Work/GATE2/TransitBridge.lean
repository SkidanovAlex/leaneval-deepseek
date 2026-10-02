/-
# GATE2 — the floored uniform lock-step transit, from PARIMPL2's universal-box form

Reviewer item 1 of the GATE2 area was: *"`Work.PARIMPL.TransitLockstepAbove` must become a PARIMPL
field beside `UT`"*.  This module closes it in the form the sibling area has actually delivered:
PARIMPL2's `Work.PARIMPL2.LockstepAll` (`Submission/Work/PARIMPL2/ExitTracking.lean`) is the
design's lock-step transit with the box origin `X₁` **universal**, and the floored form
`Work.GATE2.UTfloor` (= `Work.GATE2.TransitLockstepAbove`, the name quoted by
`Submission/Work/PARIMPL2/ExitTrackingBridge.lean`) is an immediate specialisation: instantiate
`LockstepAll`'s universal `X₁` at the prescribed floor.

So the floor hypothesis of the D1 chain is **not** an extra PARIMPL field: it follows from
PARIMPL2's single implosion export `Work.PARIMPL2.LavaursPhase`
(`Submission/Work/PARIMPL2/Lavaurs/Defs.lean`), which packages `LockstepAll` for the exact phase
transit `transPh P x₀ θ` at the height `v = x₀ − nIn`.

* `Work.GATE2.UTfloor` — the floored predicate (alias of `TransitLockstepAbove`).
* `Work.GATE2.utfloor_of_lockstepAll` — `LockstepAll ⟹ UTfloor` at any prescribed floor.
* `Work.GATE2.utfloorAll_of_lockstepAll` — the `∀ X, UTfloor … (X+1) …` form the drives consume.
-/
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.PARIMPL2.ExitTracking

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

/-- **`Work.GATE2.UTfloor` — the floored uniform lock-step transit.**  The name quoted by
`Submission/Work/PARIMPL2/ExitTrackingBridge.lean`; it *is* `Work.GATE2.TransitLockstepAbove`
(`Submission/Work/GATE2/ExitPathInputs.lean`): PARIMPL's `TransitLockstep` with the box origin
`X₁` required to lie above the caller-prescribed floor `Xb` (which D1 needs, because PL's
`PrincipalParam.far` is available only on `{Re > X}`). -/
abbrev UTfloor (c₀ : ℂ) (Nm : Set ℂ) (trans : ℂ → ℂ) (nIn : ℕ) (Ft : ℂ → ℂ → ℂ)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) (Xb v : ℝ) : Prop :=
  TransitLockstepAbove c₀ Nm trans nIn Ft Pa φa Ψ Xb v

/-- **The floored lock-step transit follows from PARIMPL2's universal-box form.**  `LockstepAll`
quantifies over *every* bounded box, so plugging its universal origin at the prescribed floor
`Xb` gives `UTfloor`. -/
theorem utfloor_of_lockstepAll {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {nIn : ℕ}
    {Ft : ℂ → ℂ → ℂ} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {v : ℝ}
    (h : Work.PARIMPL2.LockstepAll c₀ Nm trans nIn Ft Pa φa Ψ v) (Xb : ℝ) :
    UTfloor c₀ Nm trans nIn Ft Pa φa Ψ Xb v := by
  intro H W Xo η hη
  obtain ⟨ρ, hρ, hρ'⟩ := h H W Xo η Xb hη
  exact ⟨Xb, ρ, le_refl Xb, hρ, hρ'⟩

/-- The form the D1 chain consumes: the floor is itself quantified (`∀ X, … (X + 1) …`), because
PL's threshold `hPL.X` is only known after the parametrisation is built. -/
theorem utfloorAll_of_lockstepAll {c₀ : ℂ} {Nm : Set ℂ} {trans : ℂ → ℂ} {nIn : ℕ}
    {Ft : ℂ → ℂ → ℂ} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {v : ℝ}
    (h : Work.PARIMPL2.LockstepAll c₀ Nm trans nIn Ft Pa φa Ψ v) :
    ∀ X : ℝ, UTfloor c₀ Nm trans nIn Ft Pa φa Ψ (X + 1) v :=
  fun _ => utfloor_of_lockstepAll h _

end Work.GATE2
