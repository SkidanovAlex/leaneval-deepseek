/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2 — `RN0` from its two geometric obligations

`NOTES_LEAD_mandelbar_seed.md` §4.2, item `RN0`.  The rotation-number-zero statement decomposes
into

* a **real-analysis core** — a `×1024` orbit which is strictly monotone inside an arc of length
  `≤ 1` is impossible (`Rotation/rotation_monotone_eq_self.lean` and
  `Rotation/rotation_monotone_eq_self_mono.lean`, proved), and
* two **geometric obligations** on the tails of the landing rays:
  `ArcBoundAt d` — all iterates of an angle of `A` stay in a *fixed* arc of the circle (the region
  of the tail in the repelling cylinder has a bounded arc; this is the region↔arc correspondence,
  provable from the side-preservation of the `α`-pair, see `Rotation/arcBound_of_sidePreserve`),
  and `AngleMonoAt d` — if `1024 θ ≢ θ (mod 1)`, the iterated angles are strictly monotone (the
  tail order `O` together with the correspondence `M`).

This file states that decomposition and proves the implication, both for a single parameter and in
the global form used by the assembly.
-/
import Mathlib
import Submission.Work.SeedSimple2.Main
import Submission.Work.SeedSimple2.Rotation.rotation_monotone_eq_self
import Submission.Work.SeedSimple2.Rotation.rotation_monotone_eq_self_mono

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedSimple2.Rotation

/-- **The arc bound** of `RN0` at one parameter: every iterate `1024^n θ (mod 1)` of an angle `θ`
landing at `z₁` stays in a fixed arc of the circle of length `≤ 1`. -/
def ArcBoundAt {c : ℂ} (d : Work.EL.RootParabolic c) : Prop :=
  ∀ θ ∈ Work.SeedSimple2.LandAngles d.hN d.z₁,
    ∃ c0 d0 : ℝ, d0 ≤ c0 + 1 ∧ ∀ n : ℕ,
      Int.fract ((1024 : ℝ) ^ n * θ - Work.EL.alpha1) ∈ Set.Ioo c0 d0

/-- **The angle monotonicity** of `RN0` at one parameter: if `1024 θ ≢ θ`, the iterated angles are
strictly monotone (in one of the two directions, the orientation being supplied by the geometry of
the tail order). -/
def AngleMonoAt {c : ℂ} (d : Work.EL.RootParabolic c) : Prop :=
  ∀ θ ∈ Work.SeedSimple2.LandAngles d.hN d.z₁, Int.fract (1024 * θ) ≠ θ →
    ((∀ n : ℕ, Int.fract ((1024 : ℝ) ^ n * θ - Work.EL.alpha1)
        < Int.fract ((1024 : ℝ) ^ (n + 1) * θ - Work.EL.alpha1)) ∨
      (∀ n : ℕ, Int.fract ((1024 : ℝ) ^ (n + 1) * θ - Work.EL.alpha1)
        < Int.fract ((1024 : ℝ) ^ n * θ - Work.EL.alpha1)))

/-- **`RN0` at one parameter, from the two geometric obligations.** -/
theorem rotationZero_at {c : ℂ} (d : Work.EL.RootParabolic c)
    (hArc : ArcBoundAt d) (hMono : AngleMonoAt d) :
    ∀ θ ∈ Work.SeedSimple2.LandAngles d.hN d.z₁, Int.fract (1024 * θ) = θ := by
  intro θ hθ
  by_contra hne
  obtain ⟨c0, d0, hcd, harc⟩ := hArc θ hθ
  exact rotation_monotone_eq_self_mono hcd harc (hMono θ hθ hne)

/-- The global arc bound (used by the assembly's `Prop` interface). -/
def arcBound : Prop := ∀ {c : ℂ} (d : Work.EL.RootParabolic c), ArcBoundAt d

/-- The global angle monotonicity. -/
def angleMono : Prop := ∀ {c : ℂ} (d : Work.EL.RootParabolic c), AngleMonoAt d

/-- **`RN0` from the two geometric obligations.** -/
theorem rotationZero_of_step (hArc : arcBound) (hMono : angleMono) :
    Work.SeedSimple2.rotationZero :=
  fun {c} d θ hθ => rotationZero_at d (hArc d) (hMono d) θ hθ

end Work.SeedSimple2.Rotation

end
