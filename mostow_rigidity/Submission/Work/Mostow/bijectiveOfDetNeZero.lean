import Mathlib

namespace Work.Mostow

/-- A continuous linear endomorphism of a finite-dimensional real space with nonzero determinant is
bijective. -/
theorem bijectiveOfDetNeZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (h : A.det ≠ 0) :
    Function.Bijective A := by
  -- `ContinuousLinearMap.det` is by definition the determinant of the underlying linear map.
  have h1 : LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 := h
  -- A nonzero determinant forces the kernel to be trivial.
  have h2 : (A : E →ₗ[ℝ] E).ker = ⊥ := by
    by_contra hk
    exact h1 ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hk)
  have hinj : Function.Injective (A : E →ₗ[ℝ] E) := LinearMap.ker_eq_bot.mp h2
  -- An injective endomorphism of a finite-dimensional space is surjective.
  have hsurj : Function.Surjective (A : E →ₗ[ℝ] E) := LinearMap.surjective_of_injective hinj
  exact ⟨hinj, hsurj⟩

end Work.Mostow
