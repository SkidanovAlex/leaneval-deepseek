import Mathlib

/-!
# `OnePoint ℂ` is locally path-connected

The one-point compactification of `ℂ` is homeomorphic to the `2`-sphere
(`Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`) via
`onePointEquivSphereOfFinrankEq`, and the sphere is locally path-connected because it
carries a charted-space structure with model space `EuclideanSpace ℝ (Fin 2)`, which is a
normed space and hence locally path-connected (`ChartedSpace.locallyPathConnectedSpace`).
Local path-connectedness transfers across the homeomorphism by
`Topology.IsOpenEmbedding.locallyPathConnectedSpace`.
-/

namespace Work.Smooth.JordanSeparation

theorem onePoint_locallyPathConnected : LocallyPathConnectedSpace (OnePoint ℂ) := by
  have h : LocallyPathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) _
  have hfin : Module.finrank ℝ ℂ + 1 = Fintype.card (Fin 3) := by simp
  exact Topology.IsOpenEmbedding.locallyPathConnectedSpace
    (onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) hfin).isOpenEmbedding

end Work.Smooth.JordanSeparation
