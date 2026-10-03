import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.L62LD

/-- **Cauchy's estimate on a section ball** (the derivative bound used in Lemma 6.2).

If `σb` is holomorphic on the ball `ball ζc ρb` with `‖σb y‖ ≤ R₁` there, then for every `u` in
the smaller ball `ball ζc ρ` (`ρ < ρb`) the derivative of `σb` at `u` is bounded by
`R₁ / (ρb - ρ)`: the disc `ball u (ρb - ρ)` is still contained in `ball ζc ρb`, so Cauchy's
estimate for the first derivative applies with radius `ρb - ρ`. -/
theorem deriv_section_ball_le {ζc : ℂ} {ρ ρb R₁ : ℝ} {σb : ℂ → ℂ}
    (hρρb : ρ < ρb) (hR₁ : 0 ≤ R₁)
    (hσbd : DifferentiableOn ℂ σb (Metric.ball ζc ρb))
    (hσbR : ∀ y ∈ Metric.ball ζc ρb, ‖σb y‖ ≤ R₁) :
    ∀ u ∈ Metric.ball ζc ρ, ‖deriv σb u‖ ≤ R₁ / (ρb - ρ) := by
  intro u hu
  -- the Cauchy radius is the gap between the two balls
  have hr : 0 < ρb - ρ := sub_pos.mpr hρρb
  -- the disc of radius `ρb - ρ` around `u` is still strictly inside `ball ζc ρb`
  have hsub : Metric.closedBall u (ρb - ρ) ⊆ Metric.ball ζc ρb := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have h1 : dist z ζc ≤ dist z u + dist u ζc := dist_triangle _ _ _
    have h2 : dist u ζc < ρ := Metric.mem_ball.mp hu
    linarith
  have hclsub : closure (Metric.ball u (ρb - ρ)) ⊆ Metric.ball ζc ρb :=
    Metric.closure_ball_subset_closedBall.trans hsub
  have hd : DiffContOnCl ℂ σb (Metric.ball u (ρb - ρ)) :=
    (hσbd.mono hclsub).diffContOnCl
  have hC : ∀ z ∈ Metric.sphere u (ρb - ρ), ‖σb z‖ ≤ R₁ :=
    fun z hz => hσbR z (hsub (Metric.sphere_subset_closedBall hz))
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd hC

end Work.L62LD
