/-
# Definitions for the `d = 2` phase function `ξ`

The phase `ξ` of the `d = 2` branch of the sphere theorem is an interpolation between the
`p`-side function `Ξ ∘ rdist p` (on `{rdist p ≤ 3a/4}`), the "middle" phase `Θ ∘ τ` (on the
band where `0 < β(τ x) < 1`) and the `q`-side function `π - ϑ ∘ rdist q` (on
`{rdist q ≤ 3γ/2}`), with the two cutoffs

`A r = smoothCut (3a/4) a r`  (equal to `1` for `r ≤ 3a/4`, to `0` for `a ≤ r`) and
`B r = smoothCut (3γ/2) (3γ/2 + e/2) r` (equal to `1` for `r ≤ 3γ/2`, `0` for
`3γ/2 + e/2 ≤ r`).

This module contains only the definitions (no proofs), so that it is instantly importable.
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

namespace Work.Diff.Dim2

noncomputable section

/-- **Smooth step function.**  `smoothCut s t r` equals `1` for `r ≤ s`, `0` for `t ≤ r`
(so it is the "constant 1" function when `t ≤ s`), and is smooth with values in `[0,1]`. -/
noncomputable def smoothCut (s t r : ℝ) : ℝ :=
  1 - Real.smoothTransition ((r - s) / (t - s))

/-- **The `d = 2` phase function, as a function of the two cutoffs.**  For cutoffs `A`, `B`,
phase data `Ξ, ϑ, Θ` and "distance" functions `F`, `G`, `τ` (playing the roles of `rdist p`,
`rdist q` and the crossing time `τ`) this is

`A (F y) * Ξ (F y) + (1 - A (F y) - B (G y)) * Θ (τ y) + B (G y) * (π - ϑ (G y))`.

With `A = smoothCut (3a/4) a` and `B = smoothCut (3γ/2) (3γ/2 + e/2)` this is the phase `ξ`
of the smooth Reeb-flow proof of the `d = 2` sphere theorem: it equals `Ξ (F y)` on
`{F ≤ 3a/4}`, `π - ϑ (G y)` on `{G ≤ 3γ/2}`, and `Θ (τ y)` on the band where both cutoffs
vanish.  Writing the phase in this "shape" form lets one compute its derivative in the
direction of the Reeb field once and for all, by specialising `A` and `B` to `0` when the
corresponding transition is far away. -/
noncomputable def phaseShape {M : Type*}
    (A B Ξ ϑ Θ : ℝ → ℝ) (τ F G : M → ℝ) : M → ℝ :=
  fun y => A (F y) * Ξ (F y) + (1 - A (F y) - B (G y)) * Θ (τ y)
    + B (G y) * (Real.pi - ϑ (G y))

end

end Work.Diff.Dim2
