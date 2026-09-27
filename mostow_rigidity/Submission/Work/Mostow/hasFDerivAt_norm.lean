import Mathlib

namespace Work.Mostow

/-- The Fréchet derivative of the norm on a real inner product space at a nonzero point `x`
is the continuous linear functional `y ↦ (1/‖x‖) * ⟪x, y⟫`. -/
theorem hasFDerivAt_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x : E}
    (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) ((1 / ‖x‖) • innerSL ℝ x) x := by
  have hx' : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have h2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hx'.ne'
  -- `‖y‖ = √(‖y‖²)`, and the latter is `sqrt ∘ (fun y => ‖y‖²)`.
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt h2
  have hfun : (fun y : E => Real.sqrt (‖y‖ ^ 2)) = (fun y : E => ‖y‖) := by
    funext y; exact Real.sqrt_sq (norm_nonneg y)
  have hval : (1 / (2 * Real.sqrt (‖x‖ ^ 2))) • (2 • innerSL ℝ x) = (1 / ‖x‖) • innerSL ℝ x := by
    rw [Real.sqrt_sq hx'.le]
    ext y
    simp only [smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [hfun, hval] at h
  exact h

end Work.Mostow
