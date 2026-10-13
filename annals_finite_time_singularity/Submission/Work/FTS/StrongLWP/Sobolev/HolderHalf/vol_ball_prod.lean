import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongLWP.Sobolev.HolderHalf

/-- The ball in `ℝ × ℝ` (with the product, i.e. sup, norm) is a square, so its Lebesgue volume
is `4 r ^ 2` (as an `ℝ≥0∞`). -/
theorem vol_ball_prod (x : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (4 * r ^ 2) := by
  -- In the product (sup) metric the ball is the square product of the two balls.
  have hball : Metric.ball x r = Metric.ball x.1 r ×ˢ Metric.ball x.2 r := by
    ext y
    simp only [Metric.mem_ball, Set.mem_prod, Prod.dist_eq, max_lt_iff]
  -- The volume on a product is the product of the volumes, and `volume (ball a r) = 2 r` on `ℝ`.
  rw [hball, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    Real.volume_ball, Real.volume_ball,
    ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * r)]
  congr 1
  ring

end Work.FTS.StrongLWP.Sobolev.HolderHalf
