/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The ray path used by the Snail lemma (ledger item 5, the instantiation)

`Work.LandLeaves.noNeutralLanding_of_snailMilnor` instantiates the Snail lemma in Milnor's path
form (`Work.LandLeaves.SnailLemmaMilnor`) at a periodic dynamic ray: the path `p` is the tail of
the ray `R_c(θ)`, parametrised by "time" in such a way that the holomorphic second return map
`F = (Tsq c)^[k]` advances the parameter by `-1` (`F (p (t + 1)) = p t`), so that the *local
inverse* germ `g` of `F` at the landing point `z` advances it by `+1`:

    g (p t) = p (t + 1),        p t → z  (t → ∞).

The parametrisation is by the Böttcher level: the point `p t` is the point of the ray whose
Böttcher coordinate is `snailLevel k ρ t · e^{2πiθ}`, where

* `ρ > 1` is any fixed level (`ρ = 2` in the application) and
* `snailLevel k ρ t = exp (log ρ · exp (-(k · log 4) · t))`,

so that `snailLevel k ρ t → 1` as `t → ∞` and the exact functional relation

    snailLevel k ρ t = (snailLevel k ρ (t + 1)) ^ (4 ^ k)

holds: the inverse square-root-type iteration of `F` on levels is `r ↦ r ^ (4 ^ k)`, and the
level function is the `4 ^ k`-th root flow of the constant `ρ`.

This module only fixes the vocabulary; the properties of `snailLevel` are proved in
`Submission/Work/LandLeaves/snailLevel_props.lean` and the ray-level functional equation in
`Submission/Work/LandLeaves/rayPt_Tsq_iterate.lean`.
-/
import Mathlib
import Submission.Work.ELPull.Defs
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LandLeaves

noncomputable section

/-- **The Böttcher level of the ray path at "time" `t`**: `snailLevel k ρ t =
exp (log ρ · exp (-(k · log 4) · t))`.

It decreases from `ρ` (at `t = 0`) to `1` (as `t → ∞`), and the point of the dynamic ray with
this Böttcher level is the point `p t` of the Snail path.  The functional relation is
`snailLevel k ρ t = (snailLevel k ρ (t + 1)) ^ (4 ^ k)` (`snailLevel_props`). -/
noncomputable def snailLevel (k : ℕ) (ρ : ℝ) (t : ℝ) : ℝ :=
  Real.exp (Real.log ρ * Real.exp (-(((k : ℝ) * Real.log 4) * t)))

/-- **The point of the dynamic ray `R_c(θ)` at time `t` of the Snail path**: the ray point of
angle `θ` whose Böttcher level is `snailLevel k ρ t`.  For `hN` the dynamical Böttcher datum of
`T_c` and `t : ℕ` with `0 < k` and `ρ > 1` this is a well defined point of the escaping set
(`hN.rayPt_notMem`, `hN.Phi_rayPt`). -/
noncomputable def snailRay {c : ℂ} (hN : Work.ELPull.DynB c) (k : ℕ) (ρ : ℝ)
    (θ : ℝ) (t : ℝ) : ℂ :=
  hN.rayPt θ (snailLevel k ρ t)

end

end Work.LandLeaves
