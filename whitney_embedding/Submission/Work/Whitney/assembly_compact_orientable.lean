import Mathlib
import Submission.Work.Whitney.assembly_compact_full
import Submission.Work.Whitney.exists_simple_transverse_immersion
import Submission.Work.Whitney.exists_isSmoothOrientedAtlas_restrict
import Submission.Work.Embedding.exists_embedding_of_components

/-!
# The whole compact orientable branch of Whitney's strong embedding theorem

`Work.Whitney.exists_embedding_of_compact_of_orientedAtlas`: a **compact** smooth `n`-manifold
(`n ≥ 3`) that carries a smooth oriented atlas (i.e. is orientable) admits a smooth embedding into
`ℝ^{2n}` with injective manifold derivative.

This assembles *everything* proved so far, modulo one single input:

* `hpush` — the Whitney push, in the form "`HasAmbientPush n N` for every compact `n`-manifold `N`"
  (the conclusion of `Work.Whitney.exists_ambient_push_data`, whose construction is in progress).

The remaining ingredients are all proved in this workspace:

* the general position input `Work.Whitney.exists_simple_transverse_immersion` (a smooth immersion
  of a compact `M` into `ℝ^{2n}` with finitely many *simple transitive* double points);
* the connected branch `Work.Whitney.exists_embedding_of_compact_connected_orientable`
  (insertion + Whitney cancellation + invariant bookkeeping + iteration);
* the reduction to the connected case `Work.Embedding.exists_embedding_of_components`, with its
  `hconn` hypothesis discharged by restricting the oriented atlas to each compact connected open
  subset (`Work.Whitney.exists_isSmoothOrientedAtlas_restrict`).

The non-orientable case is *not* covered here: for a non-orientable `M` the sign comparison
`Work.Whitney.OppositeSign` (which is based on a *global* oriented atlas) is not available, and the
classical argument replaces it by a framing of the bigon (the transport of the local orientation
along the two arcs).  See the module docstring of `Submission.lean` for the state of that gap.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- **The compact orientable branch of Whitney's strong embedding theorem**, assembled end to end
modulo the Whitney push. -/
theorem exists_embedding_of_compact_of_orientedAtlas {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hpush : ∀ (U : TopologicalSpace.Opens M) [CompactSpace U], HasAmbientPush n U)
    (hOr : ∃ A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      IsSmoothOrientedAtlas A) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) e x) := by
  classical
  refine Work.Embedding.exists_embedding_of_components (n := n) (by omega) ?_
  -- `hconn`: every compact connected open subset of `M` is a compact connected `n`-manifold, and
  -- the oriented atlas restricts to it.
  intro U hUconn hUcpt
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hUcpt
  haveI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hUconn
  obtain ⟨A, hA⟩ := hOr
  obtain ⟨A', hA'⟩ := Work.Whitney.exists_isSmoothOrientedAtlas_restrict A hA U
  exact exists_embedding_of_compact_connected_orientable hn (hpush U) A' hA'
    (exists_simple_transverse_immersion (n := n) hn)

end Work.Whitney
