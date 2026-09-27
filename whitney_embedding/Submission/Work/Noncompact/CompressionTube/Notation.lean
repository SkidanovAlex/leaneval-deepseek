import Mathlib
import Submission.Work.Noncompact.CompressionTube.Defs

/-!
# Unambiguous notation for the model spaces of the tube construction

The harness elaborates lemma statements in a file that does *not* open the `Manifold`/`ContDiff`
scopes, so the scoped notations `𝓡`, `𝓘`, `ℕ∞` are not available there.  We provide plain
abbreviations for the model-with-corners of `ℝ^{n-1} × ℝ` and of `M` so that statements can be
written without the scoped notations.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff

noncomputable section

/-- The model with corners of `ℝ^n` (self corners). -/
abbrev MC (n : ℕ) : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  𝓡 n

/-- The model with corners of `ℝ` (self corners). -/
abbrev MCreal : ModelWithCorners ℝ ℝ ℝ := 𝓘(ℝ, ℝ)

/-- The model with corners of `ℝ^{n-1} × ℝ`. -/
abbrev MCprod (n : ℕ) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ)
      (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
  (𝓡 (n - 1)).prod (𝓘(ℝ, ℝ))

/-- The smoothness order `C^∞` used throughout (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, *not* the
analytic order `ω = ⊤`). -/
abbrev smoothOrder : WithTop ℕ∞ := ∞

end

end Work.Noncompact.CompressionTube
