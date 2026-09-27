import Mathlib

/-!
# From proper injective maps to embeddings

For the target `whitney_embedding` the conclusion is that the embedding `e : M → ℝ^{2n}` is an
`IsEmbedding`, i.e. a topological embedding (not necessarily a *closed* one).  For non-compact `M`
the natural way to obtain this is to build `e` as a proper map: a proper injective map has closed
range, hence is a closed embedding and in particular an embedding.

This file collects the (elementary) topological facts used in that reduction.
-/

open Function Set Topology

namespace Work.Embedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- A proper injective map is a closed embedding. -/
theorem isClosedEmbedding_of_isProperMap_injective (hf : IsProperMap f)
    (hinj : Function.Injective f) : IsClosedEmbedding f where
  __ := IsClosedEmbedding.of_continuous_injective_isClosedMap hf.continuous hinj hf.isClosedMap
  isClosed_range := hf.isClosed_range

/-- A proper injective map is an embedding. -/
theorem isEmbedding_of_isProperMap_injective (hf : IsProperMap f) (hinj : Function.Injective f) :
    IsEmbedding f :=
  (isClosedEmbedding_of_isProperMap_injective hf hinj).toIsEmbedding

end Work.Embedding
