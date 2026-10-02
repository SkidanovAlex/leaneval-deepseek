/-
# `Work.MandelWire.NoPortrait` — the wiring with the seed portrait discharged

The area `Work.SeedPortraitCert` has delivered exactly the third binder of
`Work.MandelWire.mandelbar_not_path_connected_of`:

```lean
Work.SeedPortraitCert.seedPortrait (db : Work.EL.RootParabolic Work.SeedCert.cb) :
  ∀ θ ∈ Set.Ico 0 1,
    (Work.Landing.landsAt Work.SeedCert.cb θ db.z₁ ↔
      θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2)
```

(axiom-clean: `#print axioms` gives `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).
Hence the wiring only needs the two remaining live exports, PARIMPL2's `LavaursPhase` and
SatFree's saturation.  Once those two are theorems,
`Work.MandelWire.mandelbar_not_path_connected_of_lav_sat` gives the unconditional
`¬ IsPathConnected Mandelbar` with no binder left.
-/
import Submission.Work.MandelWire.Main
import Submission.Work.SeedPortraitCert.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace Work.MandelWire

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The mandelbar is not path-connected**, modulo the two remaining live exports: PARIMPL2's
uniform lock-step transit and SatFree's saturation certificate.  The seed portrait
`hport` of `Work.MandelWire.mandelbar_not_path_connected_of` is discharged by
`Work.SeedPortraitCert.seedPortrait`, and the two classical inputs
(`Work.FatouDeg.fatouParabolicInput_degenerate`, `Work.SeedFatou.fatouCritInBasin`) are theorems. -/
theorem mandelbar_not_path_connected_of_lav_sat
    (hLav : ∀ {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : Work.PARIMPL.ParNormal d)
        (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀)
          d.z₁),
        Work.PARIMPL2.LavaursPhase d P fl.Pa fl.φa fl.Ψ
          (Work.PARIMPL.nEnter d fl.toParabolicFlower))
    (hSat : ∀ {c₀ : ℂ} (d : Work.EL.RootParabolic c₀),
        ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀)
            d.z₁,
        ∃ FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa,
          Work.GATE2.SaturatedFlower fl.toParabolicFlower FF) :
    ¬ IsPathConnected Mandelbar :=
  mandelbar_not_path_connected_of hLav hSat
    (fun db θ hθ => Work.SeedPortraitCert.seedPortrait db θ hθ)

end Work.MandelWire
