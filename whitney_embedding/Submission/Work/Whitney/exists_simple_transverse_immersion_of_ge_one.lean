import Mathlib
import Submission.Work.Whitney.exists_simple_transverse_immersion

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology
open Work.Projection

/-- **General position for a compact manifold in `ℝ^{2n}`, in every dimension `n ≥ 1`.**

The statement is that of `Work.Whitney.exists_simple_transverse_immersion`, whose proof never uses
more than `1 ≤ n`: the weak Whitney embedding `M ↪ ℝ^{2n+1}`
(`Work.Projection.exists_embedding_euclidean_of_compact`) is followed by the generic projection
`Work.Whitney.exists_good_direction`, which avoids the immersion-bad directions (Hausdorff dimension
`≤ 2n - 1`), the non-transversality-bad directions (Hausdorff dimension `≤ 2n - 1`) and the
triple-point-bad directions (Hausdorff dimension `≤ n`); all three bounds are strictly below the
dimension `2n` of the space of directions as soon as `n ≥ 1`.  The finiteness of the resulting
double point set is `Work.Embedding.finite_double_points_of_transverse` (compactness plus
transversality). -/
theorem exists_simple_transverse_immersion_of_ge_one {n : ℕ} (hn : 1 ≤ n) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    ∃ g : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      (∀ x, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g x)) ∧
      (Work.Whitney.doubleSet g).Finite ∧
      Work.Whitney.SimpleDP g ∧
      (∀ p : M × M, p ∈ Work.Whitney.doubleSet g →
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g p.1).range ⊔
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) g p.2).range = ⊤) := by
  -- Weak Whitney embedding into `ℝ^{2n+1}`, then a generic projection to `ℝ^{2n}`.
  obtain ⟨e, he, hemb, heinj⟩ := Work.Projection.exists_embedding_euclidean_of_compact n (M := M)
  obtain ⟨u, huimm, hutrans, hutriple⟩ :=
    Work.Whitney.exists_good_direction (n := n) hn e he hemb.injective heinj
  let g : M → EuclideanSpace ℝ (Fin (2 * n)) := fun x => projVec u (e x)
  have hg : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ g := by
    change ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ (⇑(projVec u) ∘ e)
    exact contMDiff_comp_clm (projVec u) e he
  have himmg : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) g x) := fun x => huimm x
  have htransg : ∀ x y : M, x ≠ y → g x = g y →
      (mfderiv (𝓡 n) (𝓡 (2 * n)) g x).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) g y).range = ⊤ :=
    fun x y hxy hgxy => hutrans x y hxy hgxy
  have hsimple : SimpleDP g := by
    intro p hp z hz
    obtain ⟨hne, heq⟩ := mem_doubleSet.mp hp
    rcases hutriple z p.1 p.2 hz heq with h | h | h
    · exact Or.inl h
    · exact absurd h hne
    · exact Or.inr h
  exact ⟨g, hg, himmg,
    Work.Embedding.finite_double_points_of_transverse g hg himmg htransg, hsimple,
    fun p hp => htransg p.1 p.2 (mem_doubleSet.mp hp).1 (mem_doubleSet.mp hp).2⟩

end Work.Whitney
