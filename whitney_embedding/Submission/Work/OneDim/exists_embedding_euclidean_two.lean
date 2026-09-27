import Mathlib
import Submission.Work.OneDim.classify_connected_one_manifold
import Submission.Work.OneDim.assembly_of_components

namespace Work.OneDim

-- THE `n = 1` CASE of the target `Submission.whitney_embedding`: every smooth 1-manifold which is
-- Hausdorff and second countable (no compactness, no connectedness, no orientability) admits a
-- smooth embedding into `ℝ²` with injective derivative.
--
-- The proof is the classical one, split into three pieces:
--  * *Classification of 1-manifolds* (`Work.OneDim.classify_connected_one_manifold`): every
--    connected component of `M` is diffeomorphic to `ℝ` (non-compact case) or to the circle
--    `Circle` (compact case).
--  * *Embedding* (`Work.OneDim.assembly_of_components`): `ℝ ↪ ℝ²` (a line) and `Circle ↪ ℝ²` (a
--    circle) are explicit smooth embeddings with nowhere-zero derivative; for a second countable
--    `M` the set of components is at most countable, so the images may be placed in pairwise
--    disjoint slots (lines `{p | p 1 = k + 1/2}` for the `ℝ` copies, circles of radius `1/4`
--    centred at `(k, 0)` for the `S¹` copies).  The assembled map is injective, immersive and
--    proper (the slots escape to infinity), hence is an embedding.
theorem exists_embedding_euclidean_two {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] :
    ∃ e : M → EuclideanSpace ℝ (Fin 2),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
      Topology.IsEmbedding e ∧
      ∀ x : M, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) e x) := by
  -- Every connected component is a connected nonempty open submanifold, hence `ℝ` or the circle.
  refine assembly_of_components (fun C hne hpre => ?_)
  haveI hne' : Nonempty ↥C := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hx⟩⟩
  haveI hpre' : PreconnectedSpace ↥C := isPreconnected_iff_preconnectedSpace.mp hpre
  haveI hconn : ConnectedSpace ↥C := isConnected_iff_connectedSpace.mp ⟨hne, hpre⟩
  exact classify_connected_one_manifold (C := ↥C)


end Work.OneDim
