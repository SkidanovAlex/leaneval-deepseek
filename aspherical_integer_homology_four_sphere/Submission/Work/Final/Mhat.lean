/-
# `Final/`: `M̂` as a closed 4-manifold, and its asphericity

The carrier of the challenge's manifold is the assembled Ratcliffe–Tschantz space `M̂` of the area
`Space`; all six instance fields of `Closed4Manifold` (`TopologicalSpace`, `T2Space`,
`SecondCountableTopology`, `ChartedSpace (EuclideanSpace ℝ (Fin 4))`, `CompactSpace`,
`ConnectedSpace`) come from `Work.Space.RTData` by typeclass inference.

The asphericity is the blueprint's

```
CH.aspherical_of_curvLe (hmet := LC.lcConn_compat) (htor := LC.lcConn_torsion)
    (CH.curvLe_all ∘ CURV.curvLe_of_models SPACE.chartGram_is_model)
```

with `LC.lcConn_compat` and `LC.lcConn_torsion` **delivered** (so not holders) and the parametric
curvature bound as the field `curvLe` of `FinalInputs`.
-/
import Submission.Work.Final.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.Topology
open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Work.Final

open Work.Space

noncomputable section

/-- **The manifold `M̂` of the challenge.**  The carrier is the assembled space of
`Work.Space.RTData`; the six instance fields are found by typeclass inference. -/
def Mhat4 [D : FinalInputs] : Closed4Manifold :=
  { carrier := D.Mhat }

/-- **`M̂` is aspherical** — Cartan–Hadamard applied to the non-positively curved metric of `M̂`.

This is exactly the blueprint's final line: the connection is the Levi-Civita connection
`Work.LeviCivita.lcConn` (already delivered), its metric compatibility and torsion freeness are
`Work.LeviCivita.lcConn_compat` and `Work.LeviCivita.lcConn_torsion` (already delivered), and the
parametric curvature bound is the field `curvLe` — the output of the curvature bridge
`Work.Curvature.curvLe_of_models`. -/
theorem isAspherical_Mhat4 [D : FinalInputs] : (Mhat4 (D := D)).IsAspherical := by
  haveI := D.mhatCov_contMDiff
  exact Work.CartanHadamard.aspherical_of_curvLe
    (E := E4) (H := E4) (I := I4) (M := D.Mhat)
    (cov := mhatCov (rt := D.rt))
    (hmet := Work.LeviCivita.lcConn_compat)
    (htor := Work.LeviCivita.lcConn_torsion)
    D.curvLe

end

end Work.Final
