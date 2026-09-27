import Mathlib
import Submission.Work.EQ.germCHelpers

namespace Work.EQ.FanTri

open Complex Metric Filter Set

/-- If `f 0 = 0` and `f'(0) = 0`, then `f` factors as `v ^ 2` times the holomorphic
`dslope (dslope f 0) 0`: `f v = v ^ 2 * dslope (dslope f 0) 0 v` for every `v`.  Both factors
of `v ^ 2` come from the two `dslope`s: `v * dslope f 0 v = f v` and
`v * dslope (dslope f 0) 0 v = dslope f 0 v - dslope f 0 0 = dslope f 0 v`. -/
lemma dslope_dslope_mul {f : ℂ → ℂ} (h0 : f 0 = 0) (h1 : deriv f 0 = 0) (v : ℂ) :
    f v = v ^ 2 * dslope (dslope f 0) 0 v := by
  have h2 : v * dslope (dslope f 0) 0 v = dslope f 0 v := by
    have h := sub_smul_dslope (dslope f 0) (0 : ℂ) v
    simp only [sub_zero, smul_eq_mul] at h
    rw [h, dslope_same, h1, sub_zero]
  calc f v = v * dslope f 0 v := (Work.EQ.mul_dslope_eq (f := f) h0).symm
    _ = v * (v * dslope (dslope f 0) 0 v) := by rw [h2]
    _ = v ^ 2 * dslope (dslope f 0) 0 v := by ring

/-- A holomorphic function on `B(0,2R)` whose value and first derivative vanish at `0` is
bounded by `4 M ‖u‖²/R²` on `B(0,R)` when `‖f‖ ≤ M` on `B(0,2R)`.  Route: write
`f u = u ^ 2 * g u` with `g = dslope (dslope f 0) 0` holomorphic (`Work.EQ.analyticAt_dslope`,
`Work.EQ.mul_dslope_eq`, `dslope_dslope_mul`), and use the maximum modulus principle
(`Complex.norm_le_of_forall_mem_frontier_norm_le`) on `ball 0 R`, where on the sphere
`‖z‖ = R` one has `‖g z‖ = ‖f z‖ / ‖z‖ ^ 2 ≤ M / R ^ 2`. -/
theorem analytic_quadratic_bound {R M : ℝ} (hR : 0 < R) (hM0 : 0 ≤ M) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 (2 * R))) (h0 : f 0 = 0) (h1 : deriv f 0 = 0)
    (hM : ∀ z ∈ Metric.ball 0 (2 * R), ‖f z‖ ≤ M) :
    ∀ u : ℂ, ‖u‖ ≤ R → ‖f u‖ ≤ (4 * M / R ^ 2) * ‖u‖ ^ 2 := by
  intro u hu
  set g : ℂ → ℂ := dslope (dslope f 0) 0 with hgdef
  have hfg : ∀ v : ℂ, f v = v ^ 2 * g v := by
    intro v
    rw [hgdef]
    exact dslope_dslope_mul h0 h1 v
  have hgan : AnalyticOnNhd ℂ g (Metric.ball 0 (2 * R)) := by
    intro z hz
    rw [hgdef]
    exact Work.EQ.analyticAt_dslope (Work.EQ.analyticAt_dslope (hf z hz))
  have hgdif : DifferentiableOn ℂ g (closure (Metric.ball (0 : ℂ) R)) :=
    hgan.differentiableOn.mono (fun z hz => by
      have hz' := closure_ball_subset_closedBall hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz'
      rw [Metric.mem_ball, dist_zero_right]
      linarith)
  have hd : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) := hgdif.diffContOnCl
  have hC : ∀ z ∈ frontier (Metric.ball (0 : ℂ) R), ‖g z‖ ≤ M / R ^ 2 := by
    intro z hz
    have hzs : z ∈ sphere (0 : ℂ) R := frontier_ball_subset_sphere hz
    rw [mem_sphere_iff_norm, sub_zero] at hzs
    have hzmem : z ∈ Metric.ball (0 : ℂ) (2 * R) := by
      rw [Metric.mem_ball, dist_zero_right]
      rw [hzs]
      linarith
    have hznz : ‖z‖ ≠ 0 := by rw [hzs]; exact hR.ne'
    have hnf : ‖f z‖ = ‖z‖ ^ 2 * ‖g z‖ := by rw [hfg z, norm_mul, norm_pow]
    have hgz : ‖g z‖ = ‖f z‖ / ‖z‖ ^ 2 := by
      rw [hnf, mul_div_cancel_left₀ _ (pow_ne_zero 2 hznz)]
    calc ‖g z‖ = ‖f z‖ / ‖z‖ ^ 2 := hgz
      _ = ‖f z‖ / R ^ 2 := by rw [hzs]
      _ ≤ M / R ^ 2 := by
          apply div_le_div_of_nonneg_right (hM z hzmem)
          positivity
  have hzu : u ∈ closure (Metric.ball (0 : ℂ) R) := by
    rw [closure_ball 0 hR.ne', Metric.mem_closedBall, dist_zero_right]
    exact hu
  have hgu : ‖g u‖ ≤ M / R ^ 2 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hC hzu
  have hRu : (0 : ℝ) < R ^ 2 := by positivity
  have hnf : ‖f u‖ = ‖u‖ ^ 2 * ‖g u‖ := by rw [hfg u, norm_mul, norm_pow]
  rw [hnf]
  have h2 : ‖u‖ ^ 2 * (M / R ^ 2) ≤ ‖u‖ ^ 2 * (4 * M / R ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    rw [div_le_div_iff_of_pos_right hRu]
    linarith
  calc ‖u‖ ^ 2 * ‖g u‖ ≤ ‖u‖ ^ 2 * (M / R ^ 2) := mul_le_mul_of_nonneg_left hgu (sq_nonneg _)
    _ ≤ ‖u‖ ^ 2 * (4 * M / R ^ 2) := h2
    _ = (4 * M / R ^ 2) * ‖u‖ ^ 2 := by ring

end Work.EQ.FanTri
