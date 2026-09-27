import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# The orthogonal complement of a null-ray direction has dimension `≥ 2`

For `n ≥ 3` and a unit vector `ξ ∈ Sph n ⊆ ℝⁿ`, the orthogonal complement of the line
`ℝ ∙ ξ` is a hyperplane of `ℝⁿ`, hence has dimension `n - 1 ≥ 2`.  This is the dimension
count that makes the space of directions at a boundary point of `ℍⁿ` non-degenerate.
-/

namespace Work.Mostow

open Submission.Mostow

theorem twoLeOrth (n : ℕ) (hn : 3 ≤ n) (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) :
    2 ≤ Module.finrank ℝ ((Submodule.span ℝ ({ξ} : Set (Submission.Mostow.E n)))ᗮ) := by
  -- `ξ` is a unit vector, hence nonzero
  have hne : ξ ≠ 0 := by
    intro h
    subst h
    simp [Submission.Mostow.Sph] at hξ
  -- the line spanned by `ξ` is one dimensional
  have h1 : Module.finrank ℝ (Submodule.span ℝ ({ξ} : Set (Submission.Mostow.E n))) = 1 :=
    finrank_span_singleton hne
  -- `E n = ℝⁿ` has dimension `n`
  have hdim : Module.finrank ℝ (Submission.Mostow.E n) = n := by
    simp [Submission.Mostow.E]
  -- dimensions of a subspace and its orthogonal complement add up to `n`
  have hsum := Submodule.finrank_add_finrank_orthogonal
    (Submodule.span ℝ ({ξ} : Set (Submission.Mostow.E n)))
  rw [h1, hdim] at hsum
  omega

end Work.Mostow
