import Mathlib
import Submission.Work.Projection.exists_projection_transverse
import Submission.Work.Embedding.finite_double_points_of_transverse
import Submission.Work.Projection.compact_embedding
import Submission.Work.Whitney.reduce_double_points_abstract

/-!
# From an embedding in `ℝ^{2n+1}` to a transverse immersion in `ℝ^{2n}`

`Work.Whitney.exists_immersion_transverse_of_embedding` is the first step of the final assembly of
Whitney's strong embedding theorem for a compact manifold: a smooth embedding `e : M → ℝ^{2n+1}`
(as produced by the weak Whitney theorem, `Work.Projection.exists_embedding_euclidean_of_compact`)
can be projected to `ℝ^{2n}` along a generic direction, and then

* the projection `g = projVec u ∘ e` is a smooth immersion,
* its double point set is **finite** (compactness + transversality,
  `Work.Embedding.finite_double_points_of_transverse`),
* every double point is **transverse** (in the intrinsic form: the two tangent images span
  `ℝ^{2n}`).

The remaining inputs of the endgame are the *simplicity* of the double points (no triple points)
and an oriented atlas of smooth charts; see `Submission.lean` for the status.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

theorem exists_immersion_transverse_of_embedding {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e) (hinj : Function.Injective e)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x)) :
    ∃ g : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ g ∧
      (∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) g x)) ∧
      (doubleSet g).Finite ∧
      (∀ p : M × M, p ∈ doubleSet g →
        (mfderiv (𝓡 n) (𝓡 (2 * n)) g p.1).range ⊔
          (mfderiv (𝓡 n) (𝓡 (2 * n)) g p.2).range = ⊤) := by
  obtain ⟨u, hu₁, hu₂⟩ := Work.Projection.exists_projection_transverse e he hinj himm
  have hg : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ (fun x => Work.Projection.projVec u (e x)) :=
    Work.Projection.contMDiff_comp_clm (Work.Projection.projVec u) e he
  refine ⟨fun x => Work.Projection.projVec u (e x), hg, hu₁, ?_, ?_⟩
  · exact Work.Embedding.finite_double_points_of_transverse _
      hg hu₁ (fun x y hxy hxy' => hu₂ x y hxy hxy')
  · intro p hp
    obtain ⟨hne, heq⟩ := mem_doubleSet.mp hp
    exact hu₂ p.1 p.2 hne heq

end Work.Whitney
