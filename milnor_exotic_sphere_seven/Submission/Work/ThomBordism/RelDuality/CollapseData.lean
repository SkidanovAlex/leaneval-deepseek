import Mathlib
import Submission.Work.ThomBordism.RelDuality.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Boundary collapse data

This file fixes the *geometric input* of `Work.ThomBordism.RelDuality.relClass_lift`: the data of a
"collapse of a neighbourhood of the boundary" of a compact manifold with boundary `M`.

* `BoundaryCollapse M` — a compact `K ⊆ int M`, a continuous self-map `ψ` of `M` that sends the
  complement of `K` into the boundary `∂M` and keeps `∂M` inside itself, together with a homotopy
  `H` from the identity to `ψ` which keeps `∂M` inside itself.

The two theorems that consume/produce this data are

* `Work.ThomBordism.RelDuality.relClass_lift_of_boundaryCollapse` (the cohomological transfer:
  `BoundaryCollapse M` implies the conclusion of `relClass_lift`), and
* `Work.ThomBordism.RelDuality.exists_boundaryCollapse` (the geometric existence statement).

## How the data is meant to be produced

Mathematically the data is produced by a collar `c : ∂M × [0,∞) ↪ M`: take `K = M ∖ c(∂M × [0,ε))`
(closed in the compact `M`, hence compact, and disjoint from `∂M`, hence inside the interior), let
`ψ` be the identity outside the collar and `c(y,t) ↦ c(y, max(0, 2t - 1))` on it (so that the half
of the collar `t < 1/2` is collapsed onto `∂M`, the part `t ≥ 1/2` is kept pointwise, and `∂M` is
fixed), and let `H` be the linear interpolation between the identity and `ψ` in the collar
coordinate.

Mathlib has no collaring theorem for manifolds with boundary, so a proof of
`exists_boundaryCollapse` has to build this collapse directly.  One route that avoids a partition of
unity is to cover `∂M` by finitely many *coordinate half-ball pieces* (each the chart preimage of a
half-ball whose centre lies on the boundary hyperplane, so that the coordinate pieces are
"vertical-convex"), and to compose one *local push* per piece: inside the `i`-th piece the push
`x ↦ e_i^{-1}(y_i(x), λ_i(x) · t_i(x))` shortens the last coordinate `t_i ≥ 0` by a factor
`λ_i(x) ∈ [0,1]` which is `0` where the piece is to be collapsed (so that the point lands on the
boundary hyperplane) and `1` near the frontier of the piece (so that the map is continuous and is
the identity outside).  With `λ_i` chosen `{0,1}`-valued along the complement of the compact set
`K`, each local push either fixes a point or lands it in `∂M`, and the composite collapses `Kᶜ` into
`∂M`.  This file's `BoundaryCollapse` is exactly the data such a construction produces.

The point of the data is the following.  Given `K`, `ψ` and `H` as above, the map `ψ` induces a map
of pairs `(M, Kᶜ) ⟶ (M, ∂M)`, hence a map
`Ψ : C^*(M, ∂M) ⟶ C^*(M, Kᶜ)` of relative cochain complexes, and `ψ` is homotopic (through maps of
pairs, by `H`) to the identity of `(M, ∂M)`, so `Ψ` splits the restriction
`C^*(M, Kᶜ) ⟶ C^*(M, ∂M)` up to homotopy, and the latter is surjective on cohomology.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology
open scoped Manifold unitInterval

namespace Work.ThomBordism.RelDuality

noncomputable section

/-- **Boundary collapse data of a compact manifold with boundary `M`.**

* `K` is a compact subset of the *interior* of `M`;
* `ψ` is a continuous self-map of `M` whose values on the complement of `K` lie in the boundary
  `∂M`, and which keeps `∂M` inside itself;
* `H` is a homotopy from the identity of `M` to `ψ` which keeps `∂M` inside itself at every time. -/
structure BoundaryCollapse (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 9) M] where
  /-- the compact set whose complement is collapsed onto the boundary -/
  K : Set M
  /-- `K` lies in the interior -/
  hK : K ⊆ {x : M | x ∉ (modelWithCornersEuclideanHalfSpace 9).boundary M}
  /-- `K` is compact -/
  hKc : IsCompact K
  /-- the collapsing self-map -/
  ψ : C(M, M)
  /-- `ψ` maps the complement of `K` into the boundary -/
  ψ_compl : ∀ x : M, x ∈ Kᶜ → ψ x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M
  /-- `ψ` keeps the boundary inside itself -/
  ψ_bdry : ∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M →
    ψ x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M
  /-- `ψ` fixes the boundary pointwise -/
  ψ_fix : ∀ x : M, x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M → ψ x = x
  /-- a homotopy from the identity to `ψ` -/
  H : (ContinuousMap.id M).Homotopy ψ
  /-- the homotopy keeps the boundary inside itself -/
  H_bdry : ∀ (t : unitInterval) (x : M),
    x ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M →
      H.toContinuousMap (t, x) ∈ (modelWithCornersEuclideanHalfSpace 9).boundary M

end

end Work.ThomBordism.RelDuality
