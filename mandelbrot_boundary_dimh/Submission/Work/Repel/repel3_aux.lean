import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.locally_inj_of_deriv_ne_zero
import Submission.Work.Repel.locally_bij_explicit

/-!
# REPEL3 auxiliaries

Two technical tools used by the assembly `Work.Repel.repel3`:

* `target_control_explicit`: `Work.Repel.target_control` with the two witnesses exhibited
  (`ρ = r/2`, `σ = (1/50)‖deriv d.φ c‖(r/2) - δ`) and the compact only *containing*
  `closedBall c (2r)`.  The explicit form matters: the assembly must know a positive lower
  bound for `σ` *before* choosing the scale `η` (the target disc `ball 0 σ` must contain the
  level-0 counting region, whose radius is `≍ 1/η`).
* `deriv_bound_on_ball`, `lipschitz_on_closedBall`: Cauchy's estimate and the mean-value bound,
  used to compare `P₁.φ u'` with `d₁.φ cbase` uniformly on the chain base disc.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- **`target_control` with explicit witnesses.**  Same hypotheses as
`Work.Repel.target_control` except that the compact need only *contain* `closedBall c (2r)`. -/
theorem target_control_explicit {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {f : ℂ → ℂ} {Df : Set ℂ} {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ}
    (P : MandelDim.PertData d f Df η y₁ K K' δ)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hderiv : deriv d.φ c ≠ 0)
    (hK' : Metric.closedBall c (2 * r) ⊆ K')
    (hsub : Metric.closedBall c r ⊆ d.Dφ)
    (hginj : Set.InjOn d.φ (Metric.ball c r))
    (hsmall : 128 * δ < r * ‖deriv d.φ c‖) :
    Set.InjOn P.φ (Metric.ball c (r / 2)) ∧
      Metric.ball (d.φ c) ((1 / 50 : ℝ) * ‖deriv d.φ c‖ * (r / 2) - δ) ⊆
        P.φ '' Metric.ball c (r / 2) ∧
      Metric.ball c (r / 2) ⊆ P.Dφ := by
  have hδpos : 0 < δ := by
    have hc : c ∈ K' := hK' (Metric.mem_closedBall_self (by linarith))
    have h := P.φ_close c hc
    have hnn : (0 : ℝ) ≤ ‖P.φ c - d.φ c‖ := norm_nonneg _
    linarith
  have hK'2 : Metric.closedBall c (2 * r) ⊆ P.Dφ := hK'.trans P.K'_sub
  have hballDφ : Metric.closedBall c r ⊆ P.Dφ :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hK'2
  have hf : DifferentiableOn ℂ P.φ (Metric.closedBall c r) := P.φ_holo.mono hballDφ
  have hg : DifferentiableOn ℂ d.φ (Metric.closedBall c r) := d.φ_holo.mono hsub
  have hclose : ∀ z ∈ Metric.closedBall c r, ‖P.φ z - d.φ z‖ ≤ δ := by
    intro z hz
    have hzK : z ∈ K' :=
      hK' (Metric.closedBall_subset_closedBall (by linarith) hz)
    exact le_of_lt (P.φ_close z hzK)
  have hmain := locally_bij_explicit (f := P.φ) (g := d.φ) (c := c) (r := r) (δ := δ)
    hr hδpos hf hg hderiv hginj hclose hsmall
  exact ⟨hmain.1, hmain.2,
    (Metric.ball_subset_ball (by linarith)).trans
      (Metric.ball_subset_closedBall.trans hballDφ)⟩

/-- **Cauchy's estimate, uniform on a ball.**  A function holomorphic on an open set containing
`closedBall c (2R)` has bounded derivative on `closedBall c R`. -/
theorem deriv_bound_on_ball {g : ℂ → ℂ} {U : Set ℂ} (hg : DifferentiableOn ℂ g U)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hsub : Metric.closedBall c (2 * R) ⊆ U) :
    ∃ D : ℝ, 0 < D ∧ ∀ z ∈ Metric.closedBall c R, ‖deriv g z‖ ≤ D := by
  obtain ⟨Cb, hCb⟩ := (isCompact_closedBall c (2 * R)).exists_bound_of_continuousOn
    ((hg.mono hsub).continuousOn)
  set C : ℝ := max Cb 1 with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨C / R, div_pos hCpos hR, ?_⟩
  intro z hz
  have hzc : ‖z - c‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hmem2 : ∀ w ∈ Metric.closedBall z R, w ∈ Metric.closedBall c (2 * R) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ R + R := by linarith
      _ = 2 * R := by ring
  have hmem : ∀ w ∈ Metric.closedBall z R, w ∈ U := fun w hw => hsub (hmem2 w hw)
  have hd : DiffContOnCl ℂ g (Metric.ball z R) := by
    refine ⟨hg.mono (fun w hw => hmem w (Metric.ball_subset_closedBall hw)), ?_⟩
    rw [closure_ball z (ne_of_gt hR)]
    exact (hg.mono hmem).continuousOn
  have hC : ∀ w ∈ Metric.sphere z R, ‖g w‖ ≤ C := by
    intro w hw
    exact le_trans (hCb w (hmem2 w (Metric.sphere_subset_closedBall hw))) (le_max_left _ _)
  have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := g) (c := z) (R := R) (C := C) hR hd hC
  exact hmain

/-- **Mean-value bound on a closed ball** from a derivative bound. -/
theorem lipschitz_on_closedBall {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U)
    {c : ℂ} {R D : ℝ} (hsub : Metric.closedBall c R ⊆ U)
    (hD : ∀ z ∈ Metric.closedBall c R, ‖deriv g z‖ ≤ D) :
    ∀ u ∈ Metric.closedBall c R, ∀ v ∈ Metric.closedBall c R, ‖g u - g v‖ ≤ D * ‖u - v‖ := by
  intro u hu v hv
  have hdiff : ∀ x ∈ Metric.closedBall c R, DifferentiableAt ℂ g x := fun x hx =>
    hg.differentiableAt (hU.mem_nhds (hsub hx))
  exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff hD (convex_closedBall c R) hv hu

/-- **`η` dominates a fixed linear function times `η`.**  For any `g : ℝ` and large `η`,
`η * g < exp (2πη)`.  (Used to place the level-1 scale `η₁ = exp (2πη)/‖s₀‖` above the
level-0 counting height `η`.) -/
theorem exists_eta_mul_lt_exp (g : ℝ) :
    ∃ B : ℝ, ∀ η : ℝ, B ≤ η → η * g < Real.exp (2 * Real.pi * η) := by
  rcases le_or_gt g 0 with hg | hg
  · refine ⟨1, fun η hη => ?_⟩
    have h1 : η * g ≤ 0 := by nlinarith [hg, le_of_lt (lt_of_lt_of_le one_pos hη)]
    have h2 : (0:ℝ) < Real.exp (2 * Real.pi * η) := Real.exp_pos _
    linarith
  · refine ⟨max 1 ((Real.log (g + 1) + 1) / (2 * Real.pi - 1) + 1), fun η hη => ?_⟩
    have hη1 : (1:ℝ) ≤ η := le_trans (le_max_left _ _) hη
    have hη0 : 0 < η := lt_of_lt_of_le one_pos hη1
    have hB : (Real.log (g + 1) + 1) / (2 * Real.pi - 1) + 1 ≤ η := le_trans (le_max_right _ _) hη
    have h2pi : (0:ℝ) < 2 * Real.pi - 1 := by linarith [Real.pi_gt_three]
    have hlogg : 0 ≤ Real.log (g + 1) := Real.log_nonneg (by linarith)
    have hB' : (Real.log (g + 1) + 1) / (2 * Real.pi - 1) ≤ η - 1 := by linarith
    have hkey : Real.log (g + 1) + 1 ≤ (2 * Real.pi - 1) * η := by
      have h := (div_le_iff₀ h2pi).mp hB'
      nlinarith [h, h2pi, hη0]
    have hgnn : (0:ℝ) < g + 1 := by linarith
    have hpos : (0:ℝ) < η * g + 1 := by nlinarith [hη0, hg]
    have hlog1 : Real.log (η * (g + 1)) = Real.log η + Real.log (g + 1) :=
      Real.log_mul (ne_of_gt hη0) (ne_of_gt hgnn)
    have hlog2 : Real.log η ≤ η - 1 := Real.log_le_sub_one_of_pos hη0
    have hle : Real.log (η * g + 1) ≤ Real.log (η * (g + 1)) := by
      apply Real.log_le_log hpos
      nlinarith [hη0]
    have hfinal : Real.log (η * g + 1) ≤ 2 * Real.pi * η := by
      calc Real.log (η * g + 1) ≤ Real.log (η * (g + 1)) := hle
        _ = Real.log η + Real.log (g + 1) := hlog1
        _ ≤ (η - 1) + Real.log (g + 1) := by linarith
        _ = η + (Real.log (g + 1) - 1) := by ring
        _ ≤ 2 * Real.pi * η := by nlinarith
    have := (Real.log_le_iff_le_exp hpos).mp hfinal
    linarith

/-- **`exp (2πη)` eventually dominates any fixed constant.** -/
theorem exists_exp_ge_const (c : ℝ) :
    ∃ B : ℝ, ∀ η : ℝ, B ≤ η → max c 1 ≤ Real.exp (2 * Real.pi * η) := by
  refine ⟨max (Real.log (max c 1) / (2 * Real.pi) + 1) 0, fun η hη => ?_⟩
  have hcm : 0 < max c 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have h1 : Real.log (max c 1) / (2 * Real.pi) + 1 ≤ η :=
    le_trans (le_max_left _ _) hη
  have h2 : Real.log (max c 1) ≤ 2 * Real.pi * η := by
    have := (div_le_iff₀ h2pi).mp (by linarith : Real.log (max c 1) / (2 * Real.pi) ≤ η)
    linarith
  exact (Real.log_le_iff_le_exp hcm).mp h2

end

end Work.Repel
