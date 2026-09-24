import Mathlib
import Submission.Work.Drive.integral_inner_gradient_logNorm_eq
import Submission.Work.Analysis.Harmonic.integral_inner_gradient_eq_zero
import Submission.Work.Drive.greenEnergyPairing

/-!
# The chart-local pole identity

If `u` agrees on a ball around `p` with `-log‖·-p‖ + H`, where `H` is harmonic on that ball, then
testing `u` against a compactly supported `C¹` function `Φ` supported in the ball gives `2π Φ p`:

This is the "`-Δu = 2π δ_p`" identity read in a chart, and the single term of the pole identity
`Q_f(χ) = 2π χ(pole)` in the energy route to the symmetry of the Green function
(`Submission/Work/Drive/greenSymmetryGeneral.lean`).
-/

open MeasureTheory Set Filter
open scoped Topology Gradient

noncomputable section

namespace Work.Drive


/-- **Growth bound of the gradient of a function that differs from `-log‖·-p‖` by a harmonic
function.**  The gradient blows up at most like the inverse distance to the pole.  This is the input
of the `L¹` facts that make the Dirichlet pairing of a Green function against a test function
absolutely convergent. -/
theorem exists_norm_gradient_le_of_logExpansion {u H : ℂ → ℝ} {p : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball p ρ))
    (hueq : ∀ z ∈ Metric.ball p ρ, z ≠ p → u z = -Real.log ‖z - p‖ + H z) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball p (ρ / 2), z ≠ p →
      ‖gradient u z‖ ≤ C / ‖z - p‖ := by
  have hcd : ContDiffOn ℝ 2 H (Metric.ball p ρ) := hH.contDiffOn
  have hfderiv_cont : ContinuousOn (fun z : ℂ => fderiv ℝ H z)
      (Metric.closedBall p (ρ / 2)) := by
    have h1 : ContinuousOn (fun z : ℂ => fderivWithin ℝ H (Metric.ball p ρ) z)
        (Metric.ball p ρ) :=
      hcd.continuousOn_fderivWithin Metric.isOpen_ball.uniqueDiffOn (by norm_num)
    refine (h1.mono (fun z hz => Metric.closedBall_subset_ball (by linarith) hz)).congr ?_
    intro z hz
    exact (fderivWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds
      (Metric.closedBall_subset_ball (by linarith) hz))).symm
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall p (ρ / 2)).exists_bound_of_continuousOn hfderiv_cont
  refine ⟨1 + max C₁ 0 * ρ, by positivity, fun z hz hzp => ?_⟩
  have hzρ : z ∈ Metric.ball p ρ := Metric.ball_subset_ball (by linarith) hz
  have h2 : (0 : ℝ) < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
  have h3 : ‖z - p‖ ≤ ρ := by
    have := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at this
    linarith
  have hdiff_neg : DifferentiableAt ℝ (fun w : ℂ => -Real.log ‖w - p‖) z :=
    (Work.Drive.hasFDerivAt_neg_log_norm_sub hzp).differentiableAt
  have hdiffH : DifferentiableAt ℝ H z := (hH z hzρ).1.differentiableAt (by norm_num)
  have hgu : gradient u z = gradient (fun w : ℂ => -Real.log ‖w - p‖) z + gradient H z := by
    rw [Filter.EventuallyEq.gradient_eq (by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzρ,
        isOpen_compl_singleton.mem_nhds (by simpa using hzp)] with w hw hwp
      exact hueq w hw hwp)]
    exact gradient_add_of_differentiableAt hdiff_neg hdiffH
  have hnorm_neg : ‖gradient (fun w : ℂ => -Real.log ‖w - p‖) z‖ = (‖z - p‖)⁻¹ := by
    rw [gradient_neg_log_norm_sub hzp, neg_smul, norm_neg, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    field_simp
  have hHle : ‖gradient H z‖ ≤ max C₁ 0 := by
    have hz' : z ∈ Metric.closedBall p (ρ / 2) := Metric.ball_subset_closedBall hz
    have h4 : ‖gradient H z‖ = ‖fderiv ℝ H z‖ := by
      simp only [gradient]
      exact (InnerProductSpace.toDual ℝ ℂ).symm.norm_map _
    rw [h4]
    exact le_trans (hC₁ z hz') (le_max_left _ _)
  have hM : 0 ≤ max C₁ 0 := le_max_right _ _
  calc ‖gradient u z‖ = ‖gradient (fun w : ℂ => -Real.log ‖w - p‖) z + gradient H z‖ := by
        rw [hgu]
    _ ≤ ‖gradient (fun w : ℂ => -Real.log ‖w - p‖) z‖ + ‖gradient H z‖ := norm_add_le _ _
    _ ≤ (‖z - p‖)⁻¹ + max C₁ 0 := add_le_add (le_of_eq hnorm_neg) hHle
    _ ≤ (1 + max C₁ 0 * ρ) / ‖z - p‖ := by
        rw [add_div, one_div]
        have h5 : max C₁ 0 ≤ max C₁ 0 * ρ / ‖z - p‖ := by
          rw [le_div_iff₀ h2]
          nlinarith [hM, h3]
        linarith

/-- **Growth bound of the gradient of the chart pullback of a function with a logarithmic pole.**
This is `exists_norm_gradient_le_of_logExpansion` read through the chart at `x₀`. -/
theorem exists_gradient_chartPull_le_of_hasLogPoleOn {X : Type*} [TopologicalSpace X]
    [T2Space X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} {x₀ : X} (hU : U ∈ 𝓝 x₀) {E : X → ℝ}
    (hharm : Submission.HarmonicOnX E (U \ {x₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn U x₀ E) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ z ∈ Metric.ball ((chartAt ℂ x₀) x₀) ρ,
      z ≠ (chartAt ℂ x₀) x₀ →
      ‖gradient (fun w : ℂ => E ((chartAt ℂ x₀).symm w)) z‖
        ≤ C / ‖z - (chartAt ℂ x₀) x₀‖ := by
  classical
  obtain ⟨ρ₀, hρ₀, H, hH, hexp⟩ :=
    Work.SimplyConnected.ABS.localPoleExpansion_of_hasLogPoleOn hU hharm hpole
  -- a radius `r` with the chart ball inside `U` and its model ball inside the chart target
  obtain ⟨r₁, hr₁pos, hr₁sub⟩ := Metric.isOpen_iff.mp (chartAt ℂ x₀).open_target _
    ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))
  obtain ⟨V, hVU, hVopen, hx₀V⟩ := mem_nhds_iff.mp hU
  have hV'open : IsOpen (V ∩ (chartAt ℂ x₀).source) :=
    hVopen.inter (chartAt ℂ x₀).open_source
  have hx₀V' : x₀ ∈ V ∩ (chartAt ℂ x₀).source := ⟨hx₀V, mem_chart_source ℂ x₀⟩
  obtain ⟨r₂, hr₂pos, hr₂sub⟩ := Metric.isOpen_iff.mp
    ((chartAt ℂ x₀).isOpen_image_of_subset_source hV'open inter_subset_right) _
    (show (chartAt ℂ x₀) x₀ ∈ (chartAt ℂ x₀) '' (V ∩ (chartAt ℂ x₀).source) from
      ⟨x₀, hx₀V', rfl⟩)
  have hpre : (chartAt ℂ x₀) ⁻¹' Metric.ball ((chartAt ℂ x₀) x₀) r₂ ∩ (chartAt ℂ x₀).source
      ⊆ U := by
    intro y hy
    obtain ⟨y', hy'mem, hy'eq⟩ := hr₂sub hy.1
    have h1 : (chartAt ℂ x₀).symm ((chartAt ℂ x₀) y)
        = (chartAt ℂ x₀).symm ((chartAt ℂ x₀) y') := by
      rw [hy'eq]
    rw [(chartAt ℂ x₀).left_inv hy.2, (chartAt ℂ x₀).left_inv hy'mem.2] at h1
    rw [h1]
    exact hVU hy'mem.1
  set δ : ℝ := min ρ₀ (min r₁ r₂) with hδdef
  have hδpos : 0 < δ := lt_min hρ₀ (lt_min hr₁pos hr₂pos)
  have hδρ₀ : δ ≤ ρ₀ := min_le_left _ _
  have hδr₁ : δ ≤ r₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδr₂ : δ ≤ r₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  have key : ∀ z ∈ Metric.ball ((chartAt ℂ x₀) x₀) δ, z ≠ (chartAt ℂ x₀) x₀ →
      (fun w : ℂ => E ((chartAt ℂ x₀).symm w)) z
        = -Real.log ‖z - (chartAt ℂ x₀) x₀‖ + H z := by
    intro z hz hzp
    have hztgt : z ∈ (chartAt ℂ x₀).target := hr₁sub (Metric.ball_subset_ball hδr₁ hz)
    have hzsrc : (chartAt ℂ x₀).symm z ∈ (chartAt ℂ x₀).source :=
      (chartAt ℂ x₀).map_target hztgt
    have hzright : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm z) = z :=
      (chartAt ℂ x₀).right_inv hztgt
    have hzU : (chartAt ℂ x₀).symm z ∈ U :=
      hpre ⟨by rw [Set.mem_preimage, hzright]; exact Metric.ball_subset_ball hδr₂ hz, hzsrc⟩
    have hne : (chartAt ℂ x₀).symm z ≠ x₀ := by
      intro h
      exact hzp (by rw [← hzright, h])
    have hcb : (chartAt ℂ x₀).symm z ∈ Submission.chartBall (chartAt ℂ x₀)
        ((chartAt ℂ x₀) x₀) ρ₀ :=
      ⟨hzsrc, by rw [Set.mem_preimage, hzright]; exact Metric.ball_subset_ball hδρ₀ hz⟩
    have hfinal := hexp ((chartAt ℂ x₀).symm z) hzU hcb hne
    rw [hzright] at hfinal
    exact hfinal
  obtain ⟨C, hCpos, hC⟩ := exists_norm_gradient_le_of_logExpansion (p := (chartAt ℂ x₀) x₀)
    (ρ := δ) (u := fun w : ℂ => E ((chartAt ℂ x₀).symm w)) hδpos
    (hH.mono (Metric.ball_subset_ball hδρ₀)) key
  exact ⟨δ / 2, C, by linarith, hCpos, fun z hz hzp => hC z hz hzp⟩

/-- **The chart-local pole identity.** -/
theorem integral_inner_gradient_of_logExpansion {u H : ℂ → ℝ} {p : ℂ} {ρ : ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball p ρ))
    (hueq : ∀ z ∈ Metric.ball p ρ, u z = -Real.log ‖z - p‖ + H z)
    {Φ : ℂ → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ)
    (hΦsupp : tsupport Φ ⊆ Metric.ball p ρ)
    (hi1 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z) (gradient Φ z)))
    (hi2 : Integrable (fun z : ℂ =>
      inner (𝕜 := ℝ) (gradient H z) (gradient Φ z))) :
    ∫ z : ℂ, inner (𝕜 := ℝ) (gradient u z) (gradient Φ z) = 2 * Real.pi * Φ p := by
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), inner (𝕜 := ℝ) (gradient u z) (gradient Φ z)
      = inner (𝕜 := ℝ) (gradient (fun y : ℂ => -Real.log ‖y - p‖) z) (gradient Φ z)
        + inner (𝕜 := ℝ) (gradient H z) (gradient Φ z) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton p)] with z hzp
    by_cases hz : z ∈ Metric.ball p ρ
    · have hev : u =ᶠ[𝓝 z] fun w => -Real.log ‖w - p‖ + H w := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
        exact hueq w hw
      have hdiff : DifferentiableAt ℝ (fun w : ℂ => -Real.log ‖w - p‖) z :=
        (Work.Drive.hasFDerivAt_neg_log_norm_sub hzp).differentiableAt
      have hHdiff : DifferentiableAt ℝ H z :=
        (hH z hz).1.differentiableAt (by norm_num)
      have h1 : gradient u z = gradient (fun w : ℂ => -Real.log ‖w - p‖) z + gradient H z := by
        rw [Filter.EventuallyEq.gradient_eq hev]
        exact gradient_add_of_differentiableAt hdiff hHdiff
      rw [h1, inner_add_left]
    · have hΦz : gradient Φ z = 0 := by
        by_contra hne
        exact hz (hΦsupp (Work.Analysis.Harmonic.tsupport_gradient_subset Φ
          (subset_closure (Function.mem_support.mpr hne))))
      simp [hΦz]
  rw [integral_congr_ae hae, integral_add hi1 hi2,
    integral_inner_gradient_logNorm_eq hΦ hΦc]
  have hzero : (∫ z : ℂ, inner (𝕜 := ℝ) (gradient H z) (gradient Φ z)) = 0 :=
    Work.Analysis.Harmonic.integral_inner_gradient_eq_zero
      (fun z hz => hH z (hΦsupp hz)) hΦ hΦc
  rw [hzero, add_zero]

end Work.Drive
