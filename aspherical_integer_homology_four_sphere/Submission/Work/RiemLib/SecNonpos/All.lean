/-
# `RiemLib/SecNonpos/All.lean` — the `sec ≤ 0` layer of the vendored library

The vendored comparison theorems (`Work.OddBound.longHomotopy.*`, `Submission.RauchK.*`, …) are
parametric in an *upper* curvature bound `K`, and they ask for a length `< π/√K`.  A manifold with
`sec ≤ 0` satisfies every upper bound `K > 0`, and `π/√K` is unbounded, so the length restriction
disappears: **every curve, and every smooth family of curves, from `p` lifts through `GExp p`**.

This module re-exports the two statements of that layer.  They are stated for

* the metric compatibility `hmet : IsMetricCompatible cov` and the torsion-freeness
  `htor : cov.torsion = 0` of the connection,
* the pointwise non-positive curvature hypothesis
  `hsec : ∀ x u v, ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 → inner ℝ (curvVec cov x u v v) u ≤ 0`
  (this is exactly `Submission.RauchK.CurvLe cov 0`), and
* the framework variable block of the vendored library (see `RiemLib/API.lean`).

Neither statement has a hypothesis on the length of the curve; the bound on the lifted curve is the
radial estimate `‖W s‖ ≤ curveLength h 0 s` (resp. `‖W s t‖ ≤ curveLength (c · t) 0 s`), which is
what makes the lift the *unique* one with `W 0 = 0` once the exponential map is shown to be a
covering map (area CH).

The two declarations are proved in the subdirectory files of the same name, each of which imports
`Submission.Work.RiemLib.API` and reduces to `Work.RiemLib.CurvLe_of_nonpos` +
`Work.RiemLib.exists_lt_pi_div_sqrt` + the corresponding `Work.OddBound.longHomotopy.*_of_short`
theorem.
-/

import Submission.Work.RiemLib.API
import Submission.Work.RiemLib.SecNonpos.exists_lift_of_short_of_nonpos
import Submission.Work.RiemLib.SecNonpos.lift_family_of_short_of_nonpos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! ## The two results — the exact signatures CH needs (`Work.RiemLib.SecNonpos`)

```
Work.RiemLib.SecNonpos.exists_lift_of_short_of_nonpos :
  IsMetricCompatible cov → cov.torsion = 0 → (sec ≤ 0) → 0 < S → ContMDiffOn 𝓘(ℝ) I 1 h (Icc 0 S) →
    h 0 = p →
      ∃ W : ℝ → TangentSpace I p, ContinuousOn W (Icc 0 S) ∧ W 0 = 0 ∧
        (∀ s ∈ Icc 0 S, GExp hmet p (W s) = h s) ∧
        (∀ s ∈ Icc 0 S, ‖W s‖ ≤ curveLength h 0 s)

Work.RiemLib.SecNonpos.lift_family_of_short_of_nonpos :
  IsMetricCompatible cov → cov.torsion = 0 → (sec ≤ 0) → 0 < S →
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (fun u ↦ c u.1 u.2) → (∀ t, c 0 t = p) →
    (∀ t ∈ Icc 0 1, curveLength (c · t) 0 S ≤ L) →
      ∃ W : ℝ → ℝ → TangentSpace I p, Continuous (fun u ↦ W u.1 u.2) ∧
        (∀ t, W 0 t = 0) ∧
        (∀ t ∈ Icc 0 1, ∀ s ∈ Icc 0 S, GExp hmet p (W s t) = c s t ∧
          ‖W s t‖ ≤ curveLength (c · t) 0 s)
```

Both live in `namespace Work.RiemLib.SecNonpos`; both assume the extra instances
`[PathConnectedSpace M] [RegularSpace M]` inherited from the Hopf–Rinow-based `_of_short` theorems.
-/

#check @Work.RiemLib.SecNonpos.exists_lift_of_short_of_nonpos
#check @Work.RiemLib.SecNonpos.lift_family_of_short_of_nonpos
