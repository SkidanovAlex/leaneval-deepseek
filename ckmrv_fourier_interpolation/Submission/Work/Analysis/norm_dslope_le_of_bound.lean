import Mathlib

namespace Work.Analysis

open Metric

/-- Cauchy-type bound for the divided slope: if `f : ℂ → ℂ` is holomorphic on the ball of
radius `2R` about `c` and bounded by `M` on the sphere of radius `R`, then the divided
slope `dslope f c x` is bounded by `2M/R` on the closed ball of radius `R`. -/
theorem norm_dslope_le_of_bound {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c (2 * R)))
    (hM : ∀ w ∈ Metric.sphere c R, ‖f w‖ ≤ M) :
    ∀ x : ℂ, ‖x - c‖ ≤ R → ‖dslope f c x‖ ≤ 2 * M / R := by
  have hRne : R ≠ 0 := hR.ne'
  have hR2 : (0 : ℝ) < 2 * R := by linarith
  -- `closedBall c R` is contained in `ball c (2R)`
  have hsub : Metric.closedBall c R ⊆ Metric.ball c (2 * R) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  have hball_sub : Metric.ball c R ⊆ Metric.ball c (2 * R) :=
    Metric.ball_subset_ball (by linarith)
  have hfR : DifferentiableOn ℂ f (Metric.ball c R) := hf.mono hball_sub
  -- Step 1: the value at the centre is also bounded by `M` (maximum modulus principle).
  have hfc : ‖f c‖ ≤ M := by
    have hd : DiffContOnCl ℂ f (Metric.ball c R) :=
      DiffContOnCl.mk_ball hfR (hf.mono hsub).continuousOn
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd ?_ ?_
    · intro z hz
      exact hM z (Metric.frontier_ball_subset_sphere hz)
    · rw [closure_ball c hRne, Metric.mem_closedBall, dist_eq_norm]
      simp only [sub_self, norm_zero]
      exact hR.le
  -- Step 2: the divided slope is bounded on the sphere of radius `R`.
  have hfront : ∀ z ∈ frontier (Metric.ball c R), ‖dslope f c z‖ ≤ 2 * M / R := by
    intro z hz
    have hzs : z ∈ Metric.sphere c R := Metric.frontier_ball_subset_sphere hz
    have hzne : z ≠ c := by
      intro h
      have hd : dist z c = R := Metric.mem_sphere.mp hzs
      rw [h, dist_self] at hd
      linarith
    have hnorm : ‖z - c‖ = R := by
      rw [← dist_eq_norm]
      exact Metric.mem_sphere.mp hzs
    have hnum : ‖f z - f c‖ ≤ 2 * M := by
      calc ‖f z - f c‖ ≤ ‖f z‖ + ‖f c‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hM z hzs) hfc
        _ = 2 * M := by ring
    calc ‖dslope f c z‖ = ‖f z - f c‖ / R := by
          rw [dslope_of_ne f hzne, slope_def_field, norm_div, hnorm]
      _ ≤ 2 * M / R := div_le_div_of_nonneg_right hnum hR.le
  -- Step 3: apply the maximum modulus principle to the divided slope.
  have hdslope : DiffContOnCl ℂ (dslope f c) (Metric.ball c R) := by
    have hmem : Metric.ball c R ∈ nhds c :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)
    have hmem2 : Metric.ball c (2 * R) ∈ nhds c :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR2)
    have hd1 : DifferentiableOn ℂ (dslope f c) (Metric.ball c R) :=
      (Complex.differentiableOn_dslope hmem).mpr hfR
    have hd2 : DifferentiableOn ℂ (dslope f c) (Metric.ball c (2 * R)) :=
      (Complex.differentiableOn_dslope hmem2).mpr hf
    exact DiffContOnCl.mk_ball hd1 (hd2.continuousOn.mono hsub)
  intro x hx
  refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdslope hfront ?_
  rw [closure_ball c hRne, Metric.mem_closedBall, dist_eq_norm]
  exact hx

end Work.Analysis
