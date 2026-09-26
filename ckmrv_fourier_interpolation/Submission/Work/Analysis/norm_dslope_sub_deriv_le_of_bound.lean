import Submission.Work.Analysis.norm_dslope_le_of_bound

namespace Work.Analysis

/-- **Maximum-modulus bound for the divided slope.**

If `f` is complex differentiable on the ball of radius `2R` around `c`, and `‖f‖ ≤ M` on the
sphere of radius `R` around `c`, then the divided slope `dslope f c` is bounded by `2M/R` on the
whole closed ball of radius `R`.

The point is that on the sphere `‖dslope f c w‖ = ‖f w - f c‖/R ≤ (M + ‖f c‖)/R ≤ 2M/R`, where
`‖f c‖ ≤ M` itself follows from the maximum modulus principle, and then the same principle applied
to the holomorphic function `dslope f c` extends the bound from the sphere to the closed ball. -/
private lemma dslope_norm_le_of_bound {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c (2 * R)))
    (hM : ∀ w ∈ Metric.sphere c R, ‖f w‖ ≤ M) :
    ∀ x : ℂ, ‖x - c‖ ≤ R → ‖dslope f c x‖ ≤ 2 * M / R := by
  have h2R : (0 : ℝ) < 2 * R := by linarith
  have hfR : DifferentiableOn ℂ f (Metric.ball c R) :=
    hf.mono (Metric.ball_subset_ball (by linarith))
  -- the closure of the ball of radius `R` sits inside the ball of radius `2R`
  have hsub : closure (Metric.ball c R) ⊆ Metric.ball c (2 * R) := by
    rw [closure_ball c hR.ne']
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  have hdcf : DiffContOnCl ℂ f (Metric.ball c R) :=
    DiffContOnCl.mk hfR (hf.continuousOn.mono hsub)
  -- bound the value at the centre
  have hfc : ‖f c‖ ≤ M := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdcf ?_ ?_
    · intro z hz
      rw [frontier_ball c hR.ne'] at hz
      exact hM z hz
    · exact subset_closure (Metric.mem_ball_self hR)
  -- bound `dslope f c` on the sphere of radius `R`
  have hsphere : ∀ w ∈ Metric.sphere c R, ‖dslope f c w‖ ≤ 2 * M / R := by
    intro w hw
    have hwnorm : ‖w - c‖ = R := mem_sphere_iff_norm.1 hw
    have hwne : w ≠ c := by
      intro h
      rw [h, sub_self, norm_zero] at hwnorm
      linarith
    have hds : dslope f c w = (f w - f c) / (w - c) := by
      rw [dslope_of_ne f hwne, slope_def_field]
    rw [hds, norm_div, hwnorm]
    have hnum : ‖f w - f c‖ ≤ 2 * M := by
      calc ‖f w - f c‖ ≤ ‖f w‖ + ‖f c‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hM w hw) hfc
        _ = 2 * M := by ring
    exact div_le_div_of_nonneg_right hnum hR.le
  -- `dslope f c` is holomorphic on the ball of radius `2R`, hence on the ball of radius `R`
  have hdG : DiffContOnCl ℂ (dslope f c) (Metric.ball c R) := by
    refine DiffContOnCl.mk ?_ ?_
    · exact (Complex.differentiableOn_dslope (Metric.ball_mem_nhds c hR)).2 hfR
    · have hbig : DifferentiableOn ℂ (dslope f c) (Metric.ball c (2 * R)) :=
        (Complex.differentiableOn_dslope (Metric.ball_mem_nhds c h2R)).2 hf
      exact hbig.continuousOn.mono hsub
  -- extend the sphere bound to the closed ball by the maximum modulus principle
  intro x hx
  have hxcl : x ∈ closure (Metric.ball c R) := by
    rw [closure_ball c hR.ne', Metric.mem_closedBall, dist_eq_norm]
    exact hx
  exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdG
    (fun z hz => hsphere z (by rwa [frontier_ball c hR.ne'] at hz)) hxcl

theorem norm_dslope_sub_deriv_le_of_bound {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c (2 * R)))
    (hM : ∀ w ∈ Metric.sphere c R, ‖f w‖ ≤ M) :
    ∀ x : ℂ, ‖x - c‖ ≤ R / 2 → ‖dslope f c x - deriv f c‖ ≤ 8 * M / R ^ 2 * ‖x - c‖ := by
  have h2R : (0 : ℝ) < 2 * R := by linarith
  -- the hypothesis on the sphere forces `M ≥ 0`
  have hM0 : 0 ≤ M := by
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c) (r := R)).2 hR.le
    exact le_trans (norm_nonneg _) (hM w hw)
  -- `dslope f c` inherits differentiability and the sphere bound
  have hGdiff : DifferentiableOn ℂ (dslope f c) (Metric.ball c (2 * R)) :=
    (Complex.differentiableOn_dslope (Metric.ball_mem_nhds c h2R)).2 hf
  have hGbound : ∀ w ∈ Metric.sphere c R, ‖dslope f c w‖ ≤ 2 * M / R :=
    fun w hw =>
      dslope_norm_le_of_bound hR hf hM w (le_of_eq (mem_sphere_iff_norm.1 hw))
  have hGle := dslope_norm_le_of_bound hR hGdiff hGbound
  intro x hx
  have hxR : ‖x - c‖ ≤ R := by linarith
  have hGx : ‖dslope (dslope f c) c x‖ ≤ 2 * (2 * M / R) / R := hGle x hxR
  -- `dslope f c x - deriv f c` is the second divided slope times `x - c`
  have hkey : (x - c) • dslope (dslope f c) c x = dslope f c x - deriv f c := by
    have h := sub_smul_dslope (dslope f c) c x
    rwa [dslope_same] at h
  rw [← hkey, norm_smul]
  have hcoef : 2 * (2 * M / R) / R ≤ 8 * M / R ^ 2 := by
    have h1 : 2 * (2 * M / R) / R = 4 * M / R ^ 2 := by
      field_simp
      ring
    rw [h1]
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ R ^ 2)
    linarith
  calc ‖x - c‖ * ‖dslope (dslope f c) c x‖
      ≤ ‖x - c‖ * (2 * (2 * M / R) / R) :=
        mul_le_mul_of_nonneg_left hGx (norm_nonneg _)
    _ ≤ ‖x - c‖ * (8 * M / R ^ 2) :=
        mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)
    _ = 8 * M / R ^ 2 * ‖x - c‖ := by ring

end Work.Analysis
