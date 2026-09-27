import Mathlib
import Submission.Work.Whitney.assembly_compact
import Submission.Work.Whitney.hasReduction

/-!
# The compact, connected, orientable branch of Whitney's theorem, reduced to three inputs

`Work.Whitney.exists_embedding_of_compact_connected_orientable` assembles the whole chapter for a
compact connected `n`-manifold (`n ≥ 3`) that *carries a smooth oriented atlas* (i.e. is
orientable), modulo exactly three inputs:

1. `Work.Whitney.HasAmbientPush` -- the Whitney push construction, i.e. the conclusion of
   `Work.Whitney.exists_ambient_push_data` (the file blocked on the push-chain file currently
   being finished);
2. `A` with `Work.Whitney.IsSmoothOrientedAtlas A` -- an oriented atlas of genuine smooth charts
   (this is where *orientability* of `M` enters; see `Submission.lean` for the non-orientable case);
3. `hgen` -- an immersion of `M` into `ℝ^{2n}` in general position: finitely many double points,
   all simple and transverse (this is the genericity input
   `Work.Whitney.exists_simple_transverse_immersion`).

Everything else -- the weak Whitney embedding, the generic projection, the insertion, the Whitney
cancellation, the invariant bookkeeping and the iteration -- is proved in this workspace.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- **The compact, connected, orientable branch of Whitney's strong embedding theorem.** -/
theorem exists_embedding_of_compact_connected_orientable {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hpush : HasAmbientPush n M)
    (A : Set (OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))))
    (hA : IsSmoothOrientedAtlas A)
    (hgen : ∃ g : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      (∀ x, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g x)) ∧
      (doubleSet g).Finite ∧ SimpleDP g ∧
      (∀ p : M × M, p ∈ doubleSet g →
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g p.1).range ⊔
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g p.2).range = ⊤)) :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) e x) :=
  exists_embedding_of_compact_connected hn
    (hasReduction_of hn (hasInsertion_of (M := M) (by omega))
      (hasCancellation_of_hasAmbientPush hpush)) A hA hgen

end Work.Whitney
