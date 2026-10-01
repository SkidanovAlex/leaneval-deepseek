import Mathlib

open Complex MeasureTheory Filter
open scoped Interval Topology

namespace Work.LinnikAreas.Density4

/-- `Re(−w) ≤ ‖w‖` for complex `w`. -/
private lemma re_neg_le_norm (w : ℂ) : (-w).re ≤ ‖w‖ := by
  calc
    (-w).re ≤ ‖-w‖ := Complex.re_le_norm (-w)
    _ = ‖w‖ := by simp

/-- A point in the unit ball around `x₀` has norm at most `‖x₀‖ + 1`. -/
private lemma norm_le_of_mem_ball (x x₀ : ℂ) (h : x ∈ Metric.ball x₀ 1) :
    ‖x‖ ≤ ‖x₀‖ + 1 := by
  have hd : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using h
  have htri : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
    have h := norm_add_le x₀ (x - x₀)
    simpa [sub_eq_add_neg] using h
  linarith

/-- Derivative of `z ↦ e^{−zt}` (complex variable `z`, parameter `t`). -/
private lemma exp_neg_mul_deriv (x t : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (-(z * t))) (Complex.exp (-(x * t)) * (-t)) x := by
  have hinner : HasDerivAt (fun z : ℂ => (-t) * z) (-t) x := by
    simpa using (hasDerivAt_id x).const_mul (-t)
  have hCe : HasDerivAt (fun z : ℂ => Complex.exp ((-t) * z))
      (Complex.exp ((-t) * x) * (-t)) x := hinner.cexp
  convert hCe using 1
  · ext z
    congr 1
    ring_nf
  · congr 1
    ring_nf

theorem laplace_interval_differentiable {a b : ℝ} {g : ℝ → ℂ}
    (hg : ContinuousOn g (Set.uIcc a b)) :
    Differentiable ℂ (fun z : ℂ => ∫ u in a..b, Complex.exp (-(z * (u : ℂ))) * g u) := by
  intro z₀
  obtain ⟨M, hM, hMnn⟩ : ∃ M : ℝ, (∀ t ∈ Set.uIcc a b, ‖g t‖ ≤ M) ∧ 0 ≤ M := by
    obtain ⟨M₀, hM₀⟩ := isCompact_uIcc.exists_bound_of_continuousOn hg
    exact ⟨max M₀ 0, fun t ht => (hM₀ t ht).trans (le_max_left _ _), le_max_right _ _⟩
  let F : ℂ → ℝ → ℂ := fun z u => Complex.exp (-(z * (u : ℂ))) * g u
  let F' : ℂ → ℝ → ℂ := fun z u => Complex.exp (-(z * (u : ℂ))) * (-(u : ℂ)) * g u
  let s : Set ℂ := Metric.ball z₀ 1
  let bound : ℝ → ℝ := fun u => Real.exp ((‖z₀‖ + 1) * ‖(u : ℂ)‖) * ‖(u : ℂ)‖ * M
  have hs : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ (by norm_num)
  have hF_meas : ∀ᶠ x in 𝓝 z₀, AEStronglyMeasurable (F x) (volume.restrict (Ι a b)) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hcont : ContinuousOn (fun u : ℝ => Complex.exp (-(x * (u : ℂ))) * g u)
        (Set.uIcc a b) :=
      ((by fun_prop : Continuous fun u : ℝ => Complex.exp (-(x * (u : ℂ)))).continuousOn).mul hg
    exact (hcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (F z₀) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ((by fun_prop : Continuous fun u : ℝ =>
      Complex.exp (-(z₀ * (u : ℂ)))).continuousOn).mul hg
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Ι a b)) := by
    have hcont : ContinuousOn (fun u : ℝ =>
        Complex.exp (-(z₀ * (u : ℂ))) * (-(u : ℂ)) * g u) (Set.uIcc a b) :=
      ((by fun_prop : Continuous fun u : ℝ =>
        Complex.exp (-(z₀ * (u : ℂ))) * (-(u : ℂ))).continuousOn).mul hg
    exact (hcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ u ∂volume, u ∈ Ι a b → ∀ x ∈ s, ‖F' x u‖ ≤ bound u := by
    refine Filter.Eventually.of_forall ?_
    intro u hu x hx
    have hxnorm : ‖x‖ ≤ ‖z₀‖ + 1 := norm_le_of_mem_ball x z₀ (by simpa [s] using hx)
    have hgu : ‖g u‖ ≤ M := hM u (Set.uIoc_subset_uIcc hu)
    have hre : (-(x * (u : ℂ))).re ≤ (‖z₀‖ + 1) * ‖(u : ℂ)‖ := by
      calc
        (-(x * (u : ℂ))).re ≤ ‖x * (u : ℂ)‖ := re_neg_le_norm (x * (u : ℂ))
        _ = ‖x‖ * ‖(u : ℂ)‖ := norm_mul x (u : ℂ)
        _ ≤ (‖z₀‖ + 1) * ‖(u : ℂ)‖ :=
            mul_le_mul_of_nonneg_right hxnorm (norm_nonneg (u : ℂ))
    have hexp : Real.exp (-(x * (u : ℂ))).re ≤ Real.exp ((‖z₀‖ + 1) * ‖(u : ℂ)‖) :=
      Real.exp_le_exp.mpr hre
    have hnorm : ‖F' x u‖ = Real.exp (-(x * (u : ℂ))).re * ‖(u : ℂ)‖ * ‖g u‖ := by
      dsimp only [F']
      simp only [norm_mul, norm_neg, Complex.norm_exp]
    rw [hnorm]
    calc
      Real.exp (-(x * (u : ℂ))).re * ‖(u : ℂ)‖ * ‖g u‖
          ≤ Real.exp ((‖z₀‖ + 1) * ‖(u : ℂ)‖) * ‖(u : ℂ)‖ * M :=
            mul_le_mul (mul_le_mul_of_nonneg_right hexp (norm_nonneg (u : ℂ))) hgu
              (norm_nonneg (g u)) (by positivity)
      _ = bound u := rfl
  have bound_cont : Continuous bound := by
    dsimp only [bound]
    fun_prop
  have bound_integrable : IntervalIntegrable bound volume a b :=
    bound_cont.intervalIntegrable a b
  have h_diff : ∀ᵐ u ∂volume, u ∈ Ι a b → ∀ x ∈ s,
      HasDerivAt (fun z : ℂ => F z u) (F' x u) x := by
    refine Filter.Eventually.of_forall ?_
    intro u _hu x _hx
    dsimp only [F, F']
    exact (exp_neg_mul_deriv x (u : ℂ)).mul_const (g u)
  obtain ⟨-, hmain⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := volume) (E := ℂ) (a := a) (b := b) (F := F) (F' := F') (x₀ := z₀)
    (s := s) (bound := bound) hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  simpa [F] using hmain.differentiableAt

end Work.LinnikAreas.Density4
