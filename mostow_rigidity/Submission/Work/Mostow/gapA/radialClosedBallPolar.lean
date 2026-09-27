import Mathlib
import Submission.Work.Mostow.radialBallPolar

namespace Work.Mostow.gapA

open MeasureTheory

/-- Polar-coordinate (radial) formula for Lebesgue measure on `EuclideanSpace ℝ (Fin m)`, `m ≥ 1`:
the integral of a radial integrand `G ‖w‖` over the **closed** ball of radius `ρ ≥ 0` equals the
surface measure of the unit sphere times `∫_{0}^{ρ} x^{m-1} G x dx`.

This is the closed-ball companion of `Work.Mostow.radialBallPolar`; the only new content is that
`closedBall 0 ρ` and `ball 0 ρ` agree up to a null set (their difference is the sphere `‖w‖ = ρ`,
a null set by `Measure.addHaar_sphere`), together with the degenerate case `ρ = 0`, where both sides
vanish. -/
theorem radialClosedBallPolar {m : ℕ} (hm : 1 ≤ m) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (G : ℝ → ENNReal) (hG : Measurable G) :
    ∫⁻ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ρ, G ‖w‖
        ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))
      = ((volume : Measure (EuclideanSpace ℝ (Fin m))).toSphere Set.univ)
        * ∫⁻ x in Set.Ioo (0 : ℝ) ρ, ENNReal.ofReal (x ^ (m - 1)) * G x ∂volume := by
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin m)) := inferInstance
  -- The closed ball and the open ball differ by the sphere of radius `ρ`, a null set.
  have hclosed : ∫⁻ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ρ, G ‖w‖
        ∂(volume : Measure (EuclideanSpace ℝ (Fin m)))
      = ∫⁻ w in Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ρ, G ‖w‖
        ∂(volume : Measure (EuclideanSpace ℝ (Fin m))) := by
    refine setLIntegral_congr ?_
    rw [ae_eq_set]
    constructor
    · rw [Metric.closedBall_sdiff_ball,
        Measure.addHaar_sphere volume (0 : EuclideanSpace ℝ (Fin m)) ρ]
    · rw [Set.sdiff_eq_empty.mpr Metric.ball_subset_closedBall, measure_empty]
  rw [hclosed]
  rcases eq_or_lt_of_le hρ with h0 | hpos
  · obtain rfl : ρ = 0 := h0.symm
    rw [Metric.ball_zero, setLIntegral_empty, Set.Ioo_self, setLIntegral_empty, mul_zero]
  · exact Work.Mostow.radialBallPolar hm ρ hpos G hG

end Work.Mostow.gapA
