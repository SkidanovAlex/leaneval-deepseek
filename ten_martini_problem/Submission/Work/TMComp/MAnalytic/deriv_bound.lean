import Mathlib

namespace Work.TMComp.MAnalytic

/-- **Uniform bound on the slice derivatives.**  If `g : ℂ → ℝ → ℂ` is jointly continuous on
`W ×ˢ univ` with `W` open, and every slice `z ↦ g z x` is holomorphic on `W`, then near any point
`z₀ ∈ W` there is a radius `r > 0` together with a constant `K ≥ 0` bounding the slice derivatives
`z ↦ deriv (fun w => g w x) z` uniformly in `x ∈ [0,1]` on the smaller disc `closedBall z₀ (r/2)`.

The proof is Cauchy's estimate: on the compact set `closedBall z₀ r ×ˢ [0,1]` the jointly continuous
`g` is bounded by some `M`; for `z ∈ closedBall z₀ (r/2)` the circle of radius `r/2` around `z`
stays inside `closedBall z₀ r ⊆ W`, so `‖deriv (fun w => g w x) z‖ ≤ M / (r/2)`. -/
theorem deriv_bound {W : Set ℂ} (hWo : IsOpen W) {g : ℂ → ℝ → ℂ}
    (hg : ContinuousOn (fun p : ℂ × ℝ => g p.1 p.2) (W ×ˢ Set.univ))
    (hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z => g z x) W) {z₀ : ℂ} (hz₀ : z₀ ∈ W) :
    ∃ r > 0, Metric.closedBall z₀ r ⊆ W ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Metric.closedBall z₀ (r / 2),
        ‖deriv (fun w => g w x) z‖ ≤ K := by
  obtain ⟨ε, hεpos, hεW⟩ := (Metric.isOpen_iff.mp hWo) z₀ hz₀
  set r : ℝ := ε / 2 with hr
  have hrpos : 0 < r := by positivity
  have hsub : Metric.closedBall z₀ r ⊆ W :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεW
  refine ⟨r, hrpos, hsub, ?_⟩
  have hcomp : IsCompact (Metric.closedBall z₀ r ×ˢ Set.Icc (0 : ℝ) 1) :=
    (isCompact_closedBall z₀ r).prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℂ × ℝ => g p.1 p.2)
      (Metric.closedBall z₀ r ×ˢ Set.Icc (0 : ℝ) 1) :=
    hg.mono (Set.prod_mono hsub (Set.subset_univ _))
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max 0 (M / (r / 2)), le_max_left _ _, ?_⟩
  intro x hx z hz
  have hR : 0 < r / 2 := by positivity
  have hcb_sub : Metric.closedBall z (r / 2) ⊆ Metric.closedBall z₀ r := by
    intro w hw
    rw [Metric.mem_closedBall] at hw ⊢
    have h2 : dist z z₀ ≤ r / 2 := Metric.mem_closedBall.mp hz
    linarith [dist_triangle w z z₀]
  have hball_sub : Metric.ball z (r / 2) ⊆ W :=
    (Metric.ball_subset_closedBall.trans hcb_sub).trans hsub
  have hsphere_sub : Metric.sphere z (r / 2) ⊆ Metric.closedBall z₀ r :=
    Metric.sphere_subset_closedBall.trans hcb_sub
  have hdiff : DiffContOnCl ℂ (fun w => g w x) (Metric.ball z (r / 2)) := by
    refine ⟨(hhol x).mono hball_sub, ?_⟩
    rw [closure_ball z (by positivity : (r / 2 : ℝ) ≠ 0)]
    have hmaps : Set.MapsTo (fun w : ℂ => (w, x)) (Metric.closedBall z (r / 2))
        (W ×ˢ Set.univ) := by
      intro w hw
      exact ⟨hsub (hcb_sub hw), Set.mem_univ x⟩
    exact hg.comp ((continuous_id.prodMk continuous_const).continuousOn) hmaps
  have hC : ∀ w ∈ Metric.sphere z (r / 2), ‖g w x‖ ≤ M := by
    intro w hw
    exact hM (w, x) ⟨hsphere_sub hw, hx⟩
  exact (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdiff hC).trans (le_max_right _ _)

end Work.TMComp.MAnalytic
