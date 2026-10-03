import Mathlib

namespace Work.Rep.Ore

/-- If `h` is self-adjoint and `h * h = star r * r + star s * s` then the norm identity
`‖h x‖^2 = ‖r x‖^2 + ‖s x‖^2` holds. -/
theorem norm_sq_eq_add_of_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (h r s : E →L[ℂ] E) (hself : star h = h) (hsq : h * h = star r * r + star s * s) (x : E) : ‖h x‖ ^ 2 = ‖r x‖ ^ 2 + ‖s x‖ ^ 2 := by
  -- Evaluate the operator identity `h * h = star r * r + star s * s` at `x`.
  have hpoint : h (h x) = star r (r x) + star s (s x) := by
    have := congrArg (fun T : E →L[ℂ] E => T x) hsq
    simpa using this
  -- `h` is self-adjoint, so `⟪h (h x), x⟫ = ⟪h x, h x⟫`.
  have h1 : inner ℂ (h (h x)) x = inner ℂ (h x) (h x) := by
    have := ContinuousLinearMap.adjoint_inner_left h x (h x)
    simp only [← ContinuousLinearMap.star_eq_adjoint, hself] at this
    exact this
  -- `star r` is the adjoint of `r`, so `⟪star r (r x), x⟫ = ⟪r x, r x⟫`.
  have h2 : inner ℂ (star r (r x)) x = inner ℂ (r x) (r x) := by
    have := ContinuousLinearMap.adjoint_inner_left r x (r x)
    simp only [← ContinuousLinearMap.star_eq_adjoint] at this
    exact this
  have h3 : inner ℂ (star s (s x)) x = inner ℂ (s x) (s x) := by
    have := ContinuousLinearMap.adjoint_inner_left s x (s x)
    simp only [← ContinuousLinearMap.star_eq_adjoint] at this
    exact this
  -- Combine: take the inner product with `x` in `hpoint`.
  have key : inner ℂ (h x) (h x) = inner ℂ (r x) (r x) + inner ℂ (s x) (s x) := by
    rw [← h1, hpoint, inner_add_left, h2, h3]
  -- Take real parts and use `(⟪y, y⟫).re = ‖y‖ ^ 2`.
  have hre := congrArg RCLike.re key
  simp only [map_add, inner_self_eq_norm_sq] at hre
  exact hre

end Work.Rep.Ore
