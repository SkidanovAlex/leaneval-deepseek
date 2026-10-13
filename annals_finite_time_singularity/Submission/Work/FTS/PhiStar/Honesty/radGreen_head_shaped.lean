import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.EllipticEst.ModalSolution.radGreen_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

/-- **Head piece, weighted by `z ^ (-r)`.**

For `r ≥ 1`, `z > 0` and `c` with `∫_0^∞ c² < ∞`, the near-origin Green integral weighted
by `z ^ (-r)` is bounded by the `L²` mass of `c`:

  `|z ^ (-r) ∫_0^z c t · t ^ (r-1) dt| ≤ √(∫_{Ioi 0} c²) · z ^ (-1/2) / √(2r-1)`.

This is `Work.EllipticEst.ModalSolution.radGreen_head_bound` (Cauchy–Schwarz for `√(c²)`
against `t ^ (r-1)` on `(0,z)` together with `∫_0^z t ^ (2r-2) = z ^ (2r-1)/(2r-1)`,
giving the unweighted bound `|∫_0^z c t ^ (r-1)| ≤ √(∫ c²) · z ^ (r - 1/2) / √(2r-1)`)
multiplied through by `z ^ (-r) > 0`, using `z ^ (-r) · z ^ (r - 1/2) = z ^ (-1/2)`. -/
theorem radGreen_head_shaped (c : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    {r z : ℝ} (hr : 1 ≤ r) (hz : 0 < z) :
    |z ^ (-r) * (∫ t in (0 : ℝ)..z, c t * t ^ (r - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * r - 1) := by
  have hzr : 0 < z ^ (-r) := Real.rpow_pos_of_pos hz _
  -- the key exponent identity, valid because `z > 0`
  have hzA : z ^ (-r) * z ^ (r - 1 / 2) = z ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hhead : |∫ t in (0 : ℝ)..z, c t * t ^ (r - 1)| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (r - 1 / 2) / Real.sqrt (2 * r - 1) :=
    Work.EllipticEst.ModalSolution.radGreen_head_bound c hc hr hz
  rw [abs_mul, abs_of_pos hzr]
  calc z ^ (-r) * |∫ t in (0 : ℝ)..z, c t * t ^ (r - 1)|
      ≤ z ^ (-r) * (Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (r - 1 / 2)
          / Real.sqrt (2 * r - 1)) :=
        mul_le_mul_of_nonneg_left hhead (le_of_lt hzr)
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * r - 1) := by
        rw [← hzA]
        ring

end Work.FTS.PhiStar.Honesty
