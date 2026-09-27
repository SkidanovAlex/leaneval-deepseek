import Mathlib
import Submission.Work.Noncompact.Compression

/-!
# The tube datum of the compression of the domain

For a non-compact connected smooth `n`-manifold `M` (`n ≥ 2`) and a locally finite set `B ⊆ M`,
the compression of the domain is built from a **locally finite family of pairwise disjoint tubes
to infinity**, one (at least) through every point of `B`:

* `CompressionTube B` is the datum: a type `ι` of tubes, and for each `i : ι` a smooth embedding
  `tube i : ℝ^{n-1} × ℝ → M` which is injective on the closed tube `‖u‖ ≤ 1`, which escapes to
  infinity in *both* `s`-directions, such that the tubes are pairwise disjoint, the family is
  locally finite, and every `b ∈ B` lies on the core `u = 0` of some tube at height `|s| ≥ 1`.

A *single* tube does not suffice: the two rays of a properly embedded line escape to at most two
ends of `M`, while a locally finite `B` may accumulate at three or more ends (e.g. `B` the points
`(1/n, 0)`, `(1 + 1/n, 0)`, `(n,0)` in `ℝ²` minus two points); a family of tubes, with the tubes
routed disjointly to the different ends, does.

The compression itself (the "u-dependent bounded shift" along each tube, glued over the locally
finite family) is constructed from this datum in
`Submission/Work/Noncompact/CompressionTube/fromTube.lean`, and the datum itself is constructed in
`Submission/Work/Noncompact/CompressionTube/existsTube.lean`.
-/

namespace Work.Noncompact

open scoped Manifold ContDiff
open Topology Set Function

/-- **The tube datum.**  A locally finite family of pairwise disjoint tubes to infinity, covering
`B` on the cores at height at least `1`. -/
structure CompressionTube (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (B : Set M) where
  /-- The index type of the tubes. -/
  ι : Type*
  /-- The tubes. -/
  tube : ι → EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M
  /-- Every tube is smooth. -/
  contMDiff_tube : ∀ i, ContMDiff ((𝓡 (n - 1)).prod 𝓘(ℝ, ℝ)) (𝓡 n) ∞ (tube i)
  /-- Every tube is a topological embedding. -/
  isEmbedding_tube : ∀ i, IsEmbedding (tube i)
  /-- Every tube is an immersion. -/
  immersion_tube : ∀ i p,
    Function.Injective (mfderiv ((𝓡 (n - 1)).prod 𝓘(ℝ, ℝ)) (𝓡 n) (tube i) p)
  /-- Every point of `B` lies on the core of some tube, at height at least `1` in absolute value. -/
  covers : B ⊆ ⋃ i, tube i '' {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | p.1 = 0 ∧ 1 ≤ |p.2|}
  /-- Every tube escapes to infinity in both `s`-directions. -/
  escapes : ∀ i (K : Set M), IsCompact K → ∃ S : ℝ,
    ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → S ≤ |p.2| → tube i p ∉ K
  /-- The tubes are pairwise disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (tube i)) (Set.range (tube j))
  /-- The family of tubes is locally finite. -/
  locallyFinite : ∀ K : Set M, IsCompact K →
    {i | ∃ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 ∧ tube i p ∈ K}.Finite

end Work.Noncompact
