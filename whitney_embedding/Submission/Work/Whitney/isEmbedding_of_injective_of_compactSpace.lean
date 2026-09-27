import Mathlib
import Submission.Work.Whitney.DoublePoint

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- A continuous injective map from a compact space to a Hausdorff space is a closed embedding.

This is the topological engine of the statement below: a closed subset of a compact space is
compact, its image under a continuous map is compact, and a compact subset of a Hausdorff space is
closed; hence the map is a closed map, and a continuous injective closed map is a closed
embedding. -/
theorem isClosedEmbedding_of_continuous_injective_of_compactSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space Y] (f : X → Y) (hf : Continuous f)
    (hinj : Function.Injective f) : IsClosedEmbedding f :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hf hinj
    (fun _ hs => (hs.isCompact.image hf).isClosed)

/-- An injective smooth map from a compact manifold is an embedding (the endgame of the compact case of Whitney's strong embedding result: once no double points remain, the map is a topological embedding). -/
theorem isEmbedding_of_injective_of_compactSpace {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    [CompactSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (hinj : Function.Injective f) : IsEmbedding f :=
  (isClosedEmbedding_of_continuous_injective_of_compactSpace f hf.continuous hinj).isEmbedding

end Work.Whitney
