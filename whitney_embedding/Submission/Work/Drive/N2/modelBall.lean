import Mathlib

/-!
# Model-chart vocabulary for the `levelSeparatingMap_far` route

`modelBall φ r` is the ball of radius `r` of a chart `φ` of a surface; `chartQ φ s₁ s₂` is the
quadratic normal form `s₁ u₀² + s₂ u₁²` of `φ`.  These two are the vocabulary shared by the
model-adapted flow (`Work.Drive.N2.exists_modelAdapted_levelFlow`) and its consumer
(`Work.Drive.N2.levelSeparatingMap_far`).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

/-- The model ball of a chart at radius `r`. -/
def modelBall {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) : Set M :=
  {y | y ∈ φ.source ∧ ‖φ y‖ < r}

/-- The quadratic normal form of a chart at a point. -/
def chartQ {M : Type*} [TopologicalSpace M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (s₁ s₂ : ℝ) (y : M) : ℝ :=
  s₁ * (φ y 0) ^ 2 + s₂ * (φ y 1) ^ 2

end Work.Drive.N2
