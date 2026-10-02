/-
# GATE2 / EXL — the exit loop for every radius below `R`, from the real-segment data

`Work.GATE2.EXL.exitLoop_of_deepSegment` produces the exit loop at *some* radius `r₀ ∈ (0,1)` from
the one-dimensional data on the real segment `[y₀−2, y₀+1]` (the `α`-deviation, the avoidance of
`K c₀`, and the oscillation bound on `ρ`).  The consumers (D1, at PARIMPL's leak radius `L.r₀`)
need it at a *prescribed* radius; `ExitLoop.mono_r₀` (the disc may be shrunk) and
`ExitLoop.congr_v` (the height is irrelevant) turn the output into the "for every radius below `R`,
at every height" form recorded here.
-/
import Submission.Work.GATE2.EXL.exitLoop_of_deepSegment
import Submission.Work.GATE2.EXL.Shrink

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

/-- **The exit loop for every radius below `R` and every height `v`, from the real-segment data.** -/
theorem exitLoop_of_deepSegment_all {c₀ : ℂ} {z₁ : ℂ}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) z₁)
    (hM : c₀ ∈ Mandelbar)
    {y₀ v α : ℝ} (hdeep : y₀ < -3)
    (hdev : ∀ x ∈ Set.Icc (y₀ - 2) (y₀ + 1),
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) α (fl.Ψ ((x : ℝ) : ℂ))| < (1 / 65536 : ℝ))
    (hoffK : ∀ x ∈ Set.Icc (y₀ - 2) (y₀ + 1), fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c₀)
    (hgr : ∀ x ∈ Set.Icc (y₀ - 2) (y₀ + 1), ∀ x' ∈ Set.Icc (y₀ - 2) (y₀ + 1),
      Work.GATE2.EXL.rho fl ((x : ℝ) : ℂ) ≤ Work.GATE2.EXL.rho fl ((x' : ℝ) : ℂ) + (1 / 32 : ℝ)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v' : ℝ,
      Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ y₀ r₀ v' α) := by
  obtain ⟨r₀, hr₀, hr₁, ⟨E⟩⟩ :=
    exitLoop_of_deepSegment (v := v) fl hM hdeep hdev hoffK hgr
  exact ⟨r₀, hr₀, fun r hr v' => ⟨ExitLoop.mono_r₀ (ExitLoop.congr_v E v') hr.2⟩⟩

end Work.GATE2.EXL
