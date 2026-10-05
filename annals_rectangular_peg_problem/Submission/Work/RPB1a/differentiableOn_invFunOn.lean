import Mathlib

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real Topology

/-- The canonical inverse of an injective holomorphic map with nonvanishing derivative is
holomorphic on the image.

Suggested route: for `y = f x` with `x ∈ U`, `deriv f x ≠ 0` makes `f` a local biholomorphism at
`x`: `AnalyticAt.hasStrictDerivAt` (from `hd.analyticAt` / `hd.analyticOnNhd hU`) turns
`deriv f x ≠ 0` into `HasStrictFDerivAt f (f' x) x` with invertible `f' x`, and
`HasStrictFDerivAt.localInverse` produces `r` with `HasStrictDerivAt r (f'(x))⁻¹ (f x)` and
`∀ᶠ y' in 𝓝 (f x), f (r y') = y'`, and `r (f x) = x` (`localInverse_apply_image`).

Since `f '' U` is open (`Work.RPB1a.isOpen_image_of_differentiableOn_of_injOn`, or the open mapping
theorem) and `f` is injective on `U`, for `y'` near `f x` inside `f '' U` we have `r y' ∈ U` and
`f (r y') = y'`, so `r y' = Function.invFunOn f U y'` (uniqueness of a preimage in `U`).  Hence
`Function.invFunOn f U =ᶠ[𝓝[f '' U] (f x)] r` and the differentiability transfers. -/
theorem differentiableOn_invFunOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f U) (hi : InjOn f U) (hne : ∀ z ∈ U, deriv f z ≠ 0) :
    DifferentiableOn ℂ (Function.invFunOn f U) (f '' U) := by
  -- `DifferentiableOn` asks for differentiability within `f '' U` at each point of `f '' U`; as the
  -- differentiability we produce at `f x` is a genuine (unrestricted) one, no openness of `f '' U`
  -- is needed.
  rintro _ ⟨x, hxU, rfl⟩
  -- `f` is analytic at `x`, hence has a strict derivative there.
  have han : AnalyticAt ℂ f x := hd.analyticOnNhd hU x hxU
  have hsd : HasStrictDerivAt f (deriv f x) x := han.hasStrictDerivAt
  have hxne : deriv f x ≠ 0 := hne x hxU
  -- The inverse function theorem gives a local inverse `r` of `f` at `x`.
  set r : ℂ → ℂ := hsd.localInverse f (deriv f x) x hxne with hr
  have hr' : HasStrictDerivAt r (deriv f x)⁻¹ (f x) := hsd.to_localInverse hxne
  have hrdiff : DifferentiableAt ℂ r (f x) := hr'.hasStrictFDerivAt.differentiableAt
  -- `f ∘ r =ᶠ id` near `f x`, and `r (f x) = x`.
  have hright : ∀ᶠ y in 𝓝 (f x), f (r y) = y := hsd.eventually_right_inverse hxne
  have hleft : r (f x) = x := by
    have h := hsd.eventually_left_inverse hxne
    rw [← hr] at h
    exact h.self_of_nhds
  -- By continuity of `r` at `f x`, the local inverse stays inside the open set `U`.
  have hUev : ∀ᶠ y in 𝓝 (f x), r y ∈ U := by
    have hcont : ContinuousAt r (f x) := hr'.hasStrictFDerivAt.continuousAt
    have : U ∈ 𝓝 (r (f x)) := by rw [hleft]; exact hU.mem_nhds hxU
    exact hcont.eventually this
  -- Uniqueness of a preimage in `U` identifies `r` with `invFunOn f U` near `f x`.
  have heq : Function.invFunOn f U =ᶠ[𝓝 (f x)] r := by
    filter_upwards [hright, hUev] with y hry hryU
    have hex : ∃ z, z ∈ U ∧ f z = y := ⟨r y, hryU, hry⟩
    exact hi (Function.invFunOn_mem hex) hryU (by rw [Function.invFunOn_eq hex, hry])
  exact (hrdiff.congr_of_eventuallyEq heq).differentiableWithinAt

end Work.RPB1a
