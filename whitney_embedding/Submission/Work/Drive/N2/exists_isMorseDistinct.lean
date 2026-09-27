import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.MorseExistence
import Submission.Work.Drive.N2.exists_distinct_criticalValues
import Submission.Work.Projection.compact_embedding

/-! Guidance from the project lead (the requester):

# Guidance (project lead) — exists_isMorseDistinct
WHY: compact n = 2 (every compact surface embeds in ℝ⁴) is the last of the three inputs of Whitney's strong
embedding theorem. The lead chose MORSE THEORY. The vocabulary is `Submission/Work/Drive/Morse.lean`: `IsCritical`,
`NondegCrit`, `IsMorseDistinct`, `HasLevelFlow`, `MorseLemma2`. Other agents prove the other pieces in parallel:
existence of Morse functions, the level flow, the planar Morse lemma, and the embedding from these. Every piece
consumes the others ONLY through those definitions, so do not change them. If one is unusable or false for your
purpose, stop and say so precisely with `declare_false`.

Route: generic height functions.
- The weak Whitney theorem is PROVED: a smooth embedding `e : M → ℝ^N` with injective derivative. Grep
  `Submission/Work/Noncompact/weak_whitney.lean` and `Submission/Work/Projection/compact_embedding.lean`.
- For v ∈ ℝ^N, the height is h_v = ⟪v, e ·⟫. The set of v for which h_v has a degenerate critical point has
  measure zero. This is Sard for the map (x, w) ↦ w on the normal bundle, or in charts: v is bad iff v = Dφ-type
  image of a map from a 2+(N-2)-1 dimensional family.
- The workspace has Hausdorff-dimension tools for exactly this kind of genericity argument (Work/Projection:
  `dimH_image_le_of_contDiffOn`, `exists_good_direction`), where it was used to pick good projection
  directions. Mathlib has `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` and
  friends.
- DISTINCT critical values: nondegenerate critical points are isolated, hence finitely many on compact M.
  Change f near each critical point by adding a small constant times a bump that is ≡ 1 near the point. Keep
  the C¹-change small so that no new critical points appear.
Keep the statement general in spirit, but you only need it for 2-dimensional M.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff in
open Work.Drive.Morse in
/-- Every compact surface carries a Morse function with distinct critical values. -/
theorem exists_isMorseDistinct {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    ∃ f : M → ℝ, IsMorseDistinct f := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · haveI : IsEmpty M := hM
    refine ⟨fun x => isEmptyElim x, fun x => isEmptyElim x, fun x => isEmptyElim x, ?_⟩
    intro x
    exact isEmptyElim x
  · haveI := hM
    obtain ⟨e, he, -, himm⟩ := Work.Projection.exists_embedding_euclidean_of_compact 2 (M := M)
    obtain ⟨f, hf, hfnd⟩ := Work.Drive.N2.exists_isMorse_of_embedding e he himm
    obtain ⟨g, hg, -, hgnd, hgdist⟩ := Work.Drive.N2.exists_distinct_criticalValues f hf hfnd
    exact ⟨g, hg, hgnd, hgdist⟩

end Work.Drive.N2
