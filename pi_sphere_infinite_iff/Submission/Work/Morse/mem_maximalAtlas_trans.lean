import Mathlib

namespace Work.Morse

open Set OpenPartialHomeomorph Manifold

/-- Composite of a chart in the maximal atlas with an element of the structure groupoid: if
`e : M → H` is compatible with the atlas of a charted space over `H` and `t : H → H` is a local
homeomorphism whose transition maps are `C^n` (i.e. `t ∈ contDiffGroupoid n I`), then `e.trans t`
is again in the maximal atlas. -/
lemma mem_maximalAtlas_trans {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
    [TopologicalSpace M] [ChartedSpace H M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M)
    {t : OpenPartialHomeomorph H H} (ht : t ∈ contDiffGroupoid n I) :
    e.trans t ∈ IsManifold.maximalAtlas I n M := by
  rw [IsManifold.mem_maximalAtlas_iff] at he ⊢
  rw [mem_maximalAtlas_iff] at he ⊢
  intro e' he'
  obtain ⟨h1, h2⟩ := he e' he'
  refine ⟨?_, ?_⟩
  · rw [trans_symm_eq_symm_trans_symm, trans_assoc]
    exact (contDiffGroupoid n I).trans ((contDiffGroupoid n I).symm ht) h1
  · rw [← trans_assoc]
    exact (contDiffGroupoid n I).trans h2 ht

end Work.Morse
