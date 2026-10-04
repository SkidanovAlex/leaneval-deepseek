import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

/-- **The primitive of a smooth function is smooth, with the expected derivative.**  For
`f : ℝ → ℝ` of class `C^∞`, the function `θ ↦ ∫ t in 0..θ, f t` is `C^∞` and its derivative is
`f`. -/
theorem contDiff_integral_deriv {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ => ∫ t in 0..θ, f t) ∧
      deriv (fun θ => ∫ t in 0..θ, f t) = f := by
  -- The primitive `F θ = ∫ t in 0..θ, f t` has derivative `f θ` at every point (the fundamental
  -- theorem of calculus, valid because `f` is continuous), hence `deriv F = f`; and since a
  -- function on `ℝ` is `C^∞` as soon as it is differentiable with `C^∞` derivative, `F` is `C^∞`.
  have hcont : Continuous f := hf.continuous
  have hderiv : ∀ θ, HasDerivAt (fun θ => ∫ t in 0..θ, f t) (f θ) θ := fun θ =>
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 θ)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hdeq : deriv (fun θ => ∫ t in 0..θ, f t) = f := funext fun θ => (hderiv θ).deriv
  refine ⟨?_, hdeq⟩
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun θ => (hderiv θ).differentiableAt, by rw [hdeq]; exact hf⟩

end Work.Diff.Dim2
