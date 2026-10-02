import Mathlib
import Submission.Work.Projective.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Projective

/-- The real dimension of the model space `Fin n → ℂ` of the affine charts is `2n`. -/
lemma finrank_real_fin_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [finrank_real_of_complex, Module.finrank_pi]
  simp

/-- The model space `Fin n → ℂ` of the affine charts of `ℂPⁿ` is linearly isomorphic to
`EuclideanSpace ℝ (Fin (2*n))` as a normed `ℝ`-vector space (its real dimension is `2n`); the
isomorphism is a diffeomorphism, which is what re-charting the atlas needs. -/
theorem nonempty_continuousLinearEquiv (n : ℕ) :
    Nonempty ((Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * n))) :=
  FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by
    rw [finrank_real_fin_complex, finrank_euclideanSpace_fin])

end Work.Projective
