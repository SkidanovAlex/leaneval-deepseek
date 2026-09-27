import Mathlib

/-!
# A direction in which a differentiable map is constant is killed by its derivative

This is the elementary but repeatedly useful fact behind the *radial* structure of the sweeps of the
counting chapter (`Submission/Work/Drive/clampedSweepChart.lean`): the projective class of a radial
sweep does not depend on the sweep parameter `x 2`, so the derivative of the class component in the
`x 2` direction vanishes.
-/

namespace Work.Drive

/-- **If a differentiable map is constant along the affine lines `t ↦ x + t • w`, then its
derivative at `x` kills `w`.** -/
theorem fderiv_apply_eq_zero_of_const_along
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : E → Z) (x : E) (w : E) (hF : DifferentiableAt ℝ F x)
    (hconst : ∀ t : ℝ, F (x + t • w) = F x) :
    fderiv ℝ F x w = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have hFx : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • w) := by
    simpa using hF.hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => F (x + t • w)) ((fderiv ℝ F x) w) 0 :=
    hFx.comp_hasDerivAt (0 : ℝ) h1
  have h4 : (fun t : ℝ => F (x + t • w)) = fun _ : ℝ => F x := funext hconst
  rw [h4] at h2
  exact h2.unique (hasDerivAt_const (0 : ℝ) (F x))

/-- The same in the form in which the sweeps use it: a map which depends only on the first two
coordinates of `ℝ³` has zero derivative in the third direction. -/
theorem fderiv_apply_single_two_eq_zero_of_dependsOn
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : EuclideanSpace ℝ (Fin 3) → Z) (x : EuclideanSpace ℝ (Fin 3))
    (hF : DifferentiableAt ℝ F x)
    (hdep : ∀ u v : EuclideanSpace ℝ (Fin 3), u 0 = v 0 → u 1 = v 1 → F u = F v) :
    fderiv ℝ F x (EuclideanSpace.single 2 (1 : ℝ)) = 0 := by
  refine fderiv_apply_eq_zero_of_const_along F x (EuclideanSpace.single 2 (1 : ℝ)) hF ?_
  intro t
  rw [hdep (x + t • EuclideanSpace.single 2 1) x (by simp) (by simp)]

end Work.Drive
