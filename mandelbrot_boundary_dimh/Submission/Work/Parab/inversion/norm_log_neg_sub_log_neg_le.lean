import Mathlib

namespace Work.Parab.inversion

/-- On a ball contained in the left-slit plane (`-x ∈ slitPlane`) and staying at distance
`≥ c` from the origin, the principal branch of the logarithm is `1/c`-Lipschitz for the
map `z ↦ log (-z)`.

This is the elementary mean-value estimate used to compare inverse Fatou coordinates:
the derivative of `z ↦ log (-z)` is `-1/(-z) = 1/z`, whose norm is `1/‖z‖ ≤ 1/c`. -/
theorem norm_log_neg_sub_log_neg_le {w : ℂ} {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (hslit : ∀ x ∈ Metric.ball w ρ, -x ∈ Complex.slitPlane)
    (hlo : ∀ x ∈ Metric.ball w ρ, c ≤ ‖x‖) :
    ∀ u ∈ Metric.ball w ρ, ∀ v ∈ Metric.ball w ρ,
      ‖Complex.log (-u) - Complex.log (-v)‖ ≤ ‖u - v‖ / c := by
  intro u hu v hv
  -- the map `z ↦ log (-z)` has derivative `(-z)⁻¹ * (-1)`, by the chain rule
  have hderiv : ∀ x ∈ Metric.ball w ρ,
      HasDerivAt (fun z : ℂ => Complex.log (-z)) ((-x)⁻¹ * (-1)) x := by
    intro x hx
    exact (Complex.hasDerivAt_log (hslit x hx)).comp x (hasDerivAt_neg x)
  have hdiff : ∀ x ∈ Metric.ball w ρ,
      DifferentiableAt ℂ (fun z : ℂ => Complex.log (-z)) x :=
    fun x hx => (hderiv x hx).differentiableAt
  -- and this derivative is bounded by `1/c` on the ball
  have hbound : ∀ x ∈ Metric.ball w ρ,
      ‖deriv (fun z : ℂ => Complex.log (-z)) x‖ ≤ c⁻¹ := by
    intro x hx
    rw [(hderiv x hx).deriv]
    simp only [norm_mul, norm_inv, norm_neg, norm_one, mul_one]
    simpa [one_div] using one_div_le_one_div_of_le hc (hlo x hx)
  -- mean value theorem on the convex ball
  have hmain := (convex_ball w ρ).norm_image_sub_le_of_norm_deriv_le hdiff hbound hv hu
  rw [div_eq_inv_mul]
  exact hmain

end Work.Parab.inversion
