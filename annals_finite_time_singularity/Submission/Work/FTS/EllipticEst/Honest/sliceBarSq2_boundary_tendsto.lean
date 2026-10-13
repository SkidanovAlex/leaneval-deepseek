import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TanTheta.wrho_deriv
import Submission.Work.FTS.EllipticEst.TanTheta.wrho_mul_sq_tendsto
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter

namespace Work.FTS.EllipticEst.Honest

/-- **The `π/2⁻` boundary term of the honest slice estimate vanishes.**

If `u θ / cos θ` has a finite limit `c` as `θ → (π/2)⁻`, then
`ρ(θ)·(u θ / cos θ)² → 0`, where `ρ = sin θ cos θ sin(2θ)^{-η}` vanishes like
`sin(2θ)^{1-η}` with `1 - η = 1/100 > 0`.

The limit `(u θ / cos θ)² → c²` is eventually bounded, so the product with `ρ → 0`
converges to `0` by `tendsto_wrho_mul_sq_zero`. -/
theorem sliceBarSq2_boundary_tendsto (u : ℝ → ℝ)
    (hlim : ∃ c : ℝ, Filter.Tendsto (fun θ => u θ / Real.cos θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c)) :
    Filter.Tendsto (fun b => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta b
        * (u b / Real.cos b) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  obtain ⟨c, hc⟩ := hlim
  -- the ratio `u θ / cos θ` is eventually bounded by `‖c‖ + 1`
  have hbdd : ∀ᶠ b in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      ‖u b / Real.cos b‖ ≤ ‖c‖ + 1 := by
    filter_upwards [hc.norm.eventually
      (eventually_lt_nhds (show ‖c‖ < ‖c‖ + 1 by linarith))] with b hb
    exact le_of_lt hb
  exact Work.FTS.EllipticEst.TanTheta.tendsto_wrho_mul_sq_zero hbdd
    (Work.FTS.EllipticEst.TanTheta.wrho_tendsto_zero_left Work.Spaces.eta
      (by linarith [Work.Spaces.eta_lt_one]))

end Work.FTS.EllipticEst.Honest
