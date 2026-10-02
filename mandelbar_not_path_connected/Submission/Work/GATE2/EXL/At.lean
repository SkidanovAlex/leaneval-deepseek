/-
# GATE2 / EXL — the exit loop at an arbitrary radius below `R` and an arbitrary height `v`

The two static constructions `Work.GATE2.EXL.exitLoop_exists` (`α₁`, the `γ₁`-lift) and
`…_iota` (`α₂`, the `γ₂`-lift) produce the exit loop at *some* radius `r₀` and *some* height `v`.
The consumers need it at PARIMPL's `LeakData.r₀` and at the real Écalle height
`v = (φa (entryPt P M.nIn c₀)).re − M.nIn`; `ExitLoop.mono_r₀` (shrinking the disc) and
`ExitLoop.congr_v` (`v` is irrelevant, the offset-avoidance being independent of it) supply both.
-/
import Submission.Work.GATE2.EXL.Shrink
import Submission.Work.GATE2.EXL.exitLoop_exists
import Submission.Work.GATE2.EXL.exitLoop_exists_iota

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

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The exit loop at any radius below `R`, at any height `v`, in the `α₁`-ray case.** -/
theorem exitLoop_at {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    {x₀ s₀ : ℝ} (hγ : L.γ₁ s₀ = ((x₀ : ℝ) : ℂ))
    (hre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₁ (s₀ - 1 + t)).re < -1)
    (hno : ∀ t ∈ Set.Icc (0 : ℝ) 1, (x₀ - 1 : ℝ) ≤ (L.γ₁ (s₀ - 1 + t)).re) :
    ∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
      Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v Work.EL.alpha1) := by
  obtain ⟨R, v₀, hR, ⟨E⟩⟩ := exitLoop_exists_of_noDip fl L hγ hre hno
  exact ⟨R, hR, fun r₀ hr v => ⟨ExitLoop.mono_r₀ (ExitLoop.congr_v E v) hr.2⟩⟩

/-- **The exit loop at any radius below `R`, at any height `v`, in the `α₂`-ray (`ι`) case.** -/
theorem exitLoop_iota_at {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    {x₀ s₀ : ℝ} (hγ : L.γ₂ s₀ = ((x₀ : ℝ) : ℂ))
    (hre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₂ (s₀ - 1 + t)).re < -1)
    (hno : ∀ t ∈ Set.Icc (0 : ℝ) 1, (x₀ - 1 : ℝ) ≤ (L.γ₂ (s₀ - 1 + t)).re) :
    ∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
      Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v Work.EL.alpha2) := by
  obtain ⟨R, v₀, hR, ⟨E⟩⟩ := exitLoop_exists_iota_of_noDip fl L hγ hre hno
  exact ⟨R, hR, fun r₀ hr v => ⟨ExitLoop.mono_r₀ (ExitLoop.congr_v E v) hr.2⟩⟩

/-- **The relaxed exit loop at any radius below `R`, at any height `v`, in the `α₁`-ray case.**

The lift hypothesis is the *crossing-only* no-dip condition of
`Work.GATE2.EXL.exitLoop_exists`: the offset-avoidance fails only at a `t` with
`Im (gamma_1 (s_0 - 1 + t)) = 0` **and** `Re (gamma_1 (s_0 - 1 + t)) <= x_0 - 3/2`.  This is
strictly weaker than the no-overshoot bound of `exitLoop_at`, which bounds `Re` at every `t`; it is
the form the design's condition (W) takes on the `alpha_1`-lift, and it is a single inequality about
the `1`-periodic shape function `s ↦ Re (gamma_1 s) - s`
(`Work.GATE2.EXL.lift_im_eq_zero_lt_of_osc` derives it from `liftOsc L < 1/4`). -/
theorem exitLoop_at_relaxed {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    {x₀ s₀ : ℝ} (hγ : L.γ₁ s₀ = ((x₀ : ℝ) : ℂ))
    (hre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₁ (s₀ - 1 + t)).re < -1)
    (hno : ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₁ (s₀ - 1 + t)).im = 0 →
      x₀ - 3 / 2 < (L.γ₁ (s₀ - 1 + t)).re) :
    ∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
      Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v Work.EL.alpha1) := by
  obtain ⟨R, v₀, hR, ⟨E⟩⟩ := exitLoop_exists fl L hγ hre hno
  exact ⟨R, hR, fun r₀ hr v => ⟨ExitLoop.mono_r₀ (ExitLoop.congr_v E v) hr.2⟩⟩

/-- **The relaxed exit loop, `α₂`-ray (`ι`) case.** -/
theorem exitLoop_iota_at_relaxed {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    {x₀ s₀ : ℝ} (hγ : L.γ₂ s₀ = ((x₀ : ℝ) : ℂ))
    (hre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₂ (s₀ - 1 + t)).re < -1)
    (hno : ∀ t ∈ Set.Icc (0 : ℝ) 1, (L.γ₂ (s₀ - 1 + t)).im = 0 →
      x₀ - 3 / 2 < (L.γ₂ (s₀ - 1 + t)).re) :
    ∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
      Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ x₀ r₀ v Work.EL.alpha2) := by
  obtain ⟨R, v₀, hR, ⟨E⟩⟩ := exitLoop_exists_iota fl L hγ hre hno
  exact ⟨R, hR, fun r₀ hr v => ⟨ExitLoop.mono_r₀ (ExitLoop.congr_v E v) hr.2⟩⟩

end Work.GATE2.EXL
