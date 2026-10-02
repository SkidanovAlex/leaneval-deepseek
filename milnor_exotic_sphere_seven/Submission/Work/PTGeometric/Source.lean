import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# PTGEOMETRIC: the compact source of the last mile, as a manifold with boundary

The last mile of the Pontryagin–Thom construction needs a compact `T2` smooth `(n+1)`-manifold with
boundary modelled on the half-space `EuclideanHalfSpace (n+1)`, on which the null-homotopy of the
collapse map avoids the base point of the Thom space, and whose boundary contains the pieces.

Mathlib has the sphere (`EuclideanSpace.instChartedSpaceSphere`, `EuclideanSpace.instIsManifoldSphere`)
and the interval (`ChartedSpace`/`instIsManifoldIcc` for `Set.Icc x y`) as manifolds, and the product
`S^n × [1,2]` — which is the natural source, since `S^n = ℝ^n ∪ {∞}` is where the pieces live — as a
product of those.  What is *not* in Mathlib is that product with the **half-space model**
`𝓡∂ (n+1)`: its product model is `(𝓡 n).prod (𝓡∂ 1)`, which is linearly equivalent to, but not
literally, the half-space model that `Work.PTGeometric.AmbientCollapseEnd` and the `Lvl/` preimage
development use.

`HalfBallSource n` below records exactly that: a type carrying the half-space model, its manifold
structure, compactness, Hausdorffness, and a homeomorphism to `S^n × [1,2]`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **The model product of the source**: the `n`-sphere times the closed interval `[1,2]`. -/
def SourceModel (n : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (1 : ℝ) 2

instance (n : ℕ) : TopologicalSpace (SourceModel n) :=
  inferInstanceAs (TopologicalSpace
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (1 : ℝ) 2))

instance (n : ℕ) : CompactSpace (SourceModel n) :=
  inferInstanceAs (CompactSpace
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (1 : ℝ) 2))

instance (n : ℕ) : T2Space (SourceModel n) :=
  inferInstanceAs (T2Space
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (1 : ℝ) 2))

/-- **The compact source of the last mile**: a compact `T2` smooth `(n+1)`-manifold with boundary
modelled on `EuclideanHalfSpace (n+1)` that is homeomorphic to `S^n × [1,2]`. -/
structure HalfBallSource (n : ℕ) where
  /-- the underlying type -/
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [isManifold : IsManifold (𝓡∂ (n + 1)) ∞ M]
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  [nonempty : Nonempty M]
  /-- the homeomorphism to the model product `S^n × [1,2]` -/
  homeo : M ≃ₜ SourceModel n

attribute [instance] HalfBallSource.topologicalSpace HalfBallSource.chartedSpace
  HalfBallSource.isManifold HalfBallSource.compactSpace HalfBallSource.t2Space
  HalfBallSource.nonempty

end

end Work.PTGeometric
