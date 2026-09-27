import Mathlib

namespace Work.KT.Fund

/-- If `r < ‖ζ‖` then the point `ζ` lies strictly outside the closed ball of radius `r` about the
origin, so `z ↦ (z - ζ)⁻¹` is holomorphic on a neighbourhood of that closed ball.  Cauchy's
integral theorem then gives that its integral around the circle `C(0, r)` vanishes. -/
theorem circleIntegral_inv_sub_eq_zero {r : ℝ} (hr : 0 < r) {ζ : ℂ} (h : r < ‖ζ‖) :
    (∮ z in C(0, r), (z - ζ)⁻¹) = 0 := by
  have hne : r ≠ 0 := ne_of_gt hr
  apply DiffContOnCl.circleIntegral_eq_zero (le_of_lt hr)
  refine ⟨?_, ?_⟩
  · apply DifferentiableOn.inv
    · exact differentiableOn_id.sub (differentiableOn_const ζ)
    · intro x hx
      have hx' : ‖x‖ < r := by simpa [dist_eq_norm] using hx
      intro hxz
      have : x = ζ := sub_eq_zero.mp hxz
      rw [this] at hx'
      linarith
  · rw [closure_ball 0 hne]
    apply ContinuousOn.inv₀
    · exact continuousOn_id.sub continuousOn_const
    · intro x hx
      have hx' : ‖x‖ ≤ r := by simpa [dist_eq_norm] using hx
      intro hxz
      have : x = ζ := sub_eq_zero.mp hxz
      rw [this] at hx'
      linarith

end Work.KT.Fund
