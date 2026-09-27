import Mathlib
import Submission.Work.Whitney.DoublePoint
import Submission.Work.Embedding.Proper

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- `doubleSet f = ∅` says exactly that two distinct points have distinct images. -/
theorem injective_of_doubleSet_eq_empty {M Y : Type*} {f : M → Y}
    (h : doubleSet f = ∅) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  have hp : (x, y) ∈ doubleSet f := ⟨hne, hxy⟩
  rw [h] at hp
  rw [Set.mem_empty_iff_false] at hp
  exact hp

/-- A proper map with no double point (`Work.Whitney.doubleSet f = ∅`, i.e. `f` is injective) is an embedding: this is the endgame of the non-compact case of Whitney's strong embedding result, where properness replaces compactness.  (Uses `Work.Embedding.isEmbedding_of_isProperMap_injective`.) -/
theorem isEmbedding_of_isProperMap_of_doubleSet_eq_empty {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hprop : IsProperMap f) (h : Work.Whitney.doubleSet f = ∅) : IsEmbedding f :=
  Work.Embedding.isEmbedding_of_isProperMap_injective hprop (injective_of_doubleSet_eq_empty h)

end Work.Whitney
