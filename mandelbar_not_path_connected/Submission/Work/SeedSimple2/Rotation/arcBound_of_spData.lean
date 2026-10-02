/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2 — the global arc bound from the side-preservation data

`Rotation/arcBound_of_sidePreserve.lean` proves the arc bound `ArcBoundAt d` for a root-parabolic
parameter whose `α`-pair is side preserving near `z₁`.  This file packages the *existence* of that
data (the `α`-pair with its specifications and the local side preservation `SP`, which is the
conclusion of the proved `ELRig.sidePreserve_of_rayCylLift`) as `SidePreserveData` and derives the
global `Rotation.arcBound`.
-/
import Mathlib
import Submission.Work.SeedSimple2.Rotation.arcBound_of_sidePreserve

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

/-- **The side-preservation data** of the `α`-pair at every root-parabolic parameter: the pair of
rays `α₁`, `α₂` co-landing at `z₁`, together with the local side preservation of its curve
(the input `SP`; `ELRig.sidePreserve_of_rayCylLift` produces it from the cylinder data). -/
def SidePreserveData : Prop :=
  ∀ {c : ℂ} (d : Work.EL.RootParabolic c), ∃ P : Work.EL.CoPair d.hN,
    P.a = Work.EL.alpha1 ∧ P.b = Work.EL.alpha2 ∧ P.y = d.z₁ ∧
      ∃ ρ > 0, ∀ z : ℂ, z ∈ Metric.ball d.z₁ ρ → z ∉ Work.EL.pairCurve P →
        (z ∈ Work.EL.pairSide P ↔ Work.FSeed.F c z ∈ Work.EL.pairSide P)

/-- **The global arc bound**, from the side-preservation data. -/
theorem arcBound_of_spData (hJ : Work.Top.JordanForm) (hD : SidePreserveData) :
    Work.SeedSimple2.Rotation.arcBound := by
  intro c d
  obtain ⟨P, hPa1, hPb1, hPy, hSP⟩ := hD d
  exact arcBound_of_sidePreserve d hJ P hPa1 hPb1 hPy hSP

end Work.SeedSimple2.Rotation

end
