import Mathlib
import Submission.Work.Drive.Morse

/-!
# Level embedding data for the `n = 2` Morse/Movie route

The MOVIE construction of `Work.Drive.N2.embedding_of_morse_movie` produces a smooth map
`g : M → ℝ³` whose restriction to every level set of the Morse function `f` is injective and whose
differential is injective on `ker (df)`.  The map `e := (g, f) : M → ℝ³ × ℝ = ℝ⁴` is then a smooth
injective immersion, hence (as `M` is compact and Hausdorff) an embedding.

This file fixes the vocabulary `Work.Drive.N2.HasLevelEmbedding` and records the elementary
consequence `Work.Drive.N2.embedding_of_level_embedding` (proved in
`Submission/Work/Drive/N2/embedding_of_level_data.lean`).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- **Level embedding data** for a function `f : M → ℝ`: a smooth map `g : M → ℝ³` which is
injective on every level set of `f` and whose differential is injective on `ker (df)` (the
"immersion along levels" condition, phrased so that `(g, f)` is an immersion at every point). -/
structure HasLevelEmbedding (f : M → ℝ) where
  /-- the map into `ℝ³` -/
  g : M → EuclideanSpace ℝ (Fin 3)
  /-- it is smooth -/
  smooth_g : ContMDiff (𝓡 2) (𝓡 3) ∞ g
  /-- it separates the points of every level set of `f` -/
  injOn_level : ∀ x y : M, f x = f y → g x = g y → x = y
  /-- `(g, f)` is an immersion -/
  imm : ∀ (x : M) (v : TangentSpace (𝓡 2) x),
    mfderiv (𝓡 2) (𝓡 3) g x v = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → v = 0

end Work.Drive.N2
