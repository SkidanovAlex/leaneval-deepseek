import Mathlib

namespace Work.Drive.Mono.intervalZeros

/-- If `f` has nonvanishing derivative on an open interval, then it is injective there.

This is the direct consequence of Rolle's theorem: two points with equal image would
force a zero of the derivative in between.  Note that no differentiability hypothesis
is needed: `deriv f x ≠ 0` already entails that `f` is differentiable at `x`, since
`deriv` is defined to be `0` where `f` is not differentiable. -/
theorem injOn_of_deriv_ne_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Set.Ioo a b, deriv f x ≠ 0) : Set.InjOn f (Set.Ioo a b) := by
  -- `a < b` only ensures the interval is nondegenerate; it is not used below.
  have _ : a < b := hab
  intro x hx y hy hxy
  -- Rolle: two points of `(a, b)` with equal image give a critical point between them.
  have key : ∀ {u v : ℝ}, u ∈ Set.Ioo a b → v ∈ Set.Ioo a b → u < v → f u = f v → False := by
    intro u v hu hv huv huvf
    have hdiff : DifferentiableOn ℝ f (Set.Icc u v) := fun z hz =>
      (differentiableAt_of_deriv_ne_zero
        (hf z ⟨lt_of_lt_of_le hu.1 hz.1, lt_of_le_of_lt hz.2 hv.2⟩)).differentiableWithinAt
    have hcont : ContinuousOn f (Set.Icc u v) := hdiff.continuousOn
    obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero huv hcont huvf
    exact hf c ⟨lt_trans hu.1 hc.1, lt_trans hc.2 hv.2⟩ hc0
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd hxy (key hx hy hlt)
  · exact heq
  · exact absurd hxy.symm (key hy hx hgt)

end Work.Drive.Mono.intervalZeros
