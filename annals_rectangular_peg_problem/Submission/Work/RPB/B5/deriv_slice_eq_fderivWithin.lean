import Mathlib

open Set

namespace Work.RPB.B5

/-- On a set of the shape `A ×ˢ univ ×ˢ B` (the middle, "time" coordinate unrestricted), the
`t`-derivative of a slice of a `C¹` function is the Fréchet derivative within the set applied to
the direction `(0,1,0)`. -/
theorem deriv_slice_eq_fderivWithin {F : ℝ × (ℝ × ℝ) → ℂ} {A B : Set ℝ}
    (hF : ContDiffOn ℝ 1 F (A ×ˢ Set.univ ×ˢ B))
    {τ t σ : ℝ} (hτ : τ ∈ A) (hσ : σ ∈ B) :
    deriv (fun u : ℝ => F (τ, u, σ)) t
      = fderivWithin ℝ F (A ×ˢ Set.univ ×ˢ B) (τ, t, σ) (0, 1, 0) := by
  -- the point lies in the set
  have hp : (τ, t, σ) ∈ (A ×ˢ Set.univ ×ˢ B) := by simp [hτ, hσ]
  -- `F` is differentiable within the set there, with derivative `fderivWithin`
  have hfd : HasFDerivWithinAt F (fderivWithin ℝ F (A ×ˢ Set.univ ×ˢ B) (τ, t, σ))
      (A ×ˢ Set.univ ×ˢ B) (τ, t, σ) :=
    ((hF.contDiffWithinAt hp).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  -- the affine slice map `u ↦ (τ, u, σ)` has derivative `(0,1,0)`
  have hline : HasDerivAt (fun u : ℝ => (τ, u, σ)) ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) t := by
    have h := (hasDerivAt_const (x := t) (c := τ)).prodMk
      ((hasDerivAt_id (t : ℝ)).prodMk (hasDerivAt_const (x := t) (c := σ)))
    simpa using h
  -- chain rule: the slice map stays in `A ×ˢ univ ×ˢ B` for every `u`, as the middle
  -- coordinate is unrestricted
  have hcomp := hfd.comp_hasFDerivAt t hline.hasFDerivAt
    (Filter.Eventually.of_forall (fun u => hp))
  have hderiv := hcomp.hasDerivAt.deriv
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hderiv

end Work.RPB.B5
