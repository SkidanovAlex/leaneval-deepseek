import Mathlib
import Submission.Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero

namespace Commons.Analysis.Complex

open Filter
open scoped Topology

/-- An analytic function at `z0` which vanishes at `z0` but is not identically zero
near `z0` is bounded below by `m * ‖w - z0‖ ^ k` on a ball around `z0`, for some
exponent `k ≥ 1` and constant `m > 0`. -/
theorem analyticAt_zero_exists_lower_bound
    {f : ℂ → ℂ} {z0 : ℂ} (hf : AnalyticAt ℂ f z0) (hz0 : f z0 = 0)
    (hnz : ¬ ∀ᶠ z in nhds z0, f z = 0) :
    ∃ (k : ℕ) (δ m : ℝ), 1 ≤ k ∧ 0 < δ ∧ 0 < m ∧
      ∀ w ∈ Metric.ball z0 δ, m * ‖w - z0‖ ^ k ≤ ‖f w‖ := by
  obtain ⟨R, k, ψ, hRpos, -, hk1, hψan, hψne, hfac⟩ :=
    exists_ball_factorization_of_analyticAt_zero (ρ := 1) zero_lt_one hf hz0 hnz
  have hz0mem : z0 ∈ Metric.ball z0 R := Metric.mem_ball_self hRpos
  have hψ0 : ψ z0 ≠ 0 := hψne z0 hz0mem
  have hψ0norm : 0 < ‖ψ z0‖ := norm_pos_iff.mpr hψ0
  -- Continuity of `ψ` at `z0` keeps `‖ψ‖` above `‖ψ z0‖ / 2` on a small ball.
  have hcont : ContinuousAt ψ z0 := (hψan z0 hz0mem).continuousAt
  have hev : ∀ᶠ w in nhds z0, ‖ψ z0‖ / 2 < ‖ψ w‖ := by
    have htend : Tendsto (fun w => ‖ψ w‖) (nhds z0) (nhds ‖ψ z0‖) := hcont.norm
    have hmem : Set.Ioi (‖ψ z0‖ / 2) ∈ nhds (‖ψ z0‖) := Ioi_mem_nhds (by linarith)
    filter_upwards [htend hmem] with w hw using hw
  obtain ⟨δ'', hδ''pos, hδ''sub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨k, min R δ'', ‖ψ z0‖ / 2, hk1, lt_min hRpos hδ''pos, by positivity, ?_⟩
  intro w hw
  have hwR : w ∈ Metric.ball z0 R := Metric.ball_subset_ball (min_le_left _ _) hw
  have hwδ'' : w ∈ Metric.ball z0 δ'' := Metric.ball_subset_ball (min_le_right _ _) hw
  have hψw : ‖ψ z0‖ / 2 < ‖ψ w‖ := hδ''sub hwδ''
  have hfaw : f w = (w - z0) ^ k * ψ w := hfac w hwR
  calc ‖ψ z0‖ / 2 * ‖w - z0‖ ^ k
      ≤ ‖ψ w‖ * ‖w - z0‖ ^ k := mul_le_mul_of_nonneg_right hψw.le (by positivity)
    _ = ‖w - z0‖ ^ k * ‖ψ w‖ := by ring
    _ = ‖f w‖ := by rw [hfaw, norm_mul, norm_pow]

end Commons.Analysis.Complex
