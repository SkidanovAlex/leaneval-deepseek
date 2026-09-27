import Mathlib
import Submission.Work.Drive.BoxParityDefs

/-!
# The graph map `u ↦ u • eᵢ + η u`

A local chart of the intersection set `K = interSet D N` at a point `q` exhibits `K` near `q` as the
graph of a map `η : ℝ → ℝ⁵` over the `i`-th coordinate: `K = {u • eᵢ + η u}` for `u` near `q i`
(`Work.Drive.exists_local_graph`).  This file introduces the graph map as a named definition and
records its basic properties; the derivative facts are in `graph_fderiv.lean`.
-/

namespace Work.Drive.ManifoldParity

open Set

noncomputable section

variable {m : ℕ}

/-- The graph map `u ↦ u • eᵢ + η u` over the `i`-th coordinate. -/
def graphMap (i : Fin (m + 1)) (η : ℝ → Work.Drive.Amb m) : ℝ → Work.Drive.Amb m :=
  fun u => u • EuclideanSpace.single i (1 : ℝ) + η u

@[simp]
theorem graphMap_apply (i : Fin (m + 1)) (η : ℝ → Work.Drive.Amb m) (u : ℝ) :
    graphMap i η u = u • EuclideanSpace.single i (1 : ℝ) + η u := rfl

/-- The `i`-th coordinate of a graph point is the parameter. -/
theorem graphMap_apply_i {i : Fin (m + 1)} {η : ℝ → Work.Drive.Amb m} (hηi : ∀ u, η u i = 0)
    (u : ℝ) : graphMap i η u i = u := by
  simp [graphMap, hηi]

/-- The difference of two graph points is the difference of their `η`-parts. -/
theorem graphMap_sub {i : Fin (m + 1)} {η : ℝ → Work.Drive.Amb m} (u v : ℝ) :
    graphMap i η u - graphMap i η v = (u - v) • EuclideanSpace.single i (1 : ℝ) + (η u - η v) := by
  rw [graphMap_apply, graphMap_apply]
  module

theorem continuous_graphMap {i : Fin (m + 1)} {η : ℝ → Work.Drive.Amb m} (h : Continuous η) :
    Continuous (graphMap i η) := by
  rw [show graphMap i η = fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u from rfl]
  exact (continuous_id.smul continuous_const).add h

theorem contDiff_graphMap {n : WithTop ℕ∞} {i : Fin (m + 1)} {η : ℝ → Work.Drive.Amb m}
    (h : ContDiff ℝ n η) : ContDiff ℝ n (graphMap i η) := by
  rw [show graphMap i η = fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u from rfl]
  exact ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).contDiff.add h)

theorem differentiableAt_graphMap {i : Fin (m + 1)} {η : ℝ → Work.Drive.Amb m} {u : ℝ}
    (h : DifferentiableAt ℝ η u) : DifferentiableAt ℝ (graphMap i η) u := by
  rw [show graphMap i η = fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u from rfl]
  exact ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).differentiableAt.add h)

end

end Work.Drive.ManifoldParity
