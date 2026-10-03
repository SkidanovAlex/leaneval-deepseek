import Mathlib
import Submission.Unif.Commons.Analysis.Complex.circleIntegral_logDeriv_eq_zero_of_analyticOnNhd_ball

open scoped Topology

/-!
# There is no analytic extension of `V` at `0` with a nonzero value

Let `V` be complex differentiable on the punctured ball `0 < ‖u‖ < ρ` and suppose that the
logarithmic derivative of `V` has circle integral `2πi` on every circle `‖u‖ = r`, `0 < r < ρ`.
Then no function `G` analytic at `0` can agree with `V` on a punctured neighbourhood of `0` and
satisfy `G 0 ≠ 0`.

Indeed, if `G` were analytic at `0` with `G 0 ≠ 0`, then `G` is analytic and zero-free on a ball
`‖z‖ < ρ₁` around `0`, and agrees with `V` on a punctured ball `0 < ‖u‖ < δ`.  On any circle
`‖z‖ = R` with `0 < R < min δ ρ₁` the functions `G` and `V` coincide near each point, so their
logarithmic derivatives agree on the circle; hence
`∮ logDeriv V = ∮ logDeriv G = 0`, contradicting `∮ logDeriv V = 2πi ≠ 0`.
-/

namespace Work.Horn

/-- If `G` and `V` agree on a punctured neighbourhood of `0`, then they agree on a genuine
punctured ball `0 < ‖u‖ < δ`. -/
lemma exists_punctured_ball_eventuallyEq {G V : ℂ → ℂ}
    (h : ∀ᶠ u : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ), G u = V u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, 0 < ‖u‖ → ‖u‖ < δ → G u = V u := by
  rw [eventually_nhdsWithin_iff] at h
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hball⟩ := h
  refine ⟨δ, hδ, fun u hu0 huδ => hball (by rwa [dist_zero_right]) ?_⟩
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (norm_ne_zero_iff.mp hu0.ne')

/-- A function that is continuous at `0` with a nonzero value there does not vanish on a ball
around `0`. -/
lemma exists_ball_ne_zero_of_continuousAt {G : ℂ → ℂ} (hc : ContinuousAt G 0) (h0 : G 0 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → G z ≠ 0 := by
  have hmem : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), G z ≠ 0 := hc.eventually_ne h0
  rw [Metric.eventually_nhds_iff] at hmem
  obtain ⟨r, hr, hr'⟩ := hmem
  exact ⟨r, hr, fun z hz => hr' (by rwa [dist_zero_right])⟩

/-- Two functions agreeing on the punctured ball `0 < ‖u‖ < δ` have the same logarithmic
derivative on every circle `‖z‖ = R` with `0 < R < δ`. -/
lemma logDeriv_eqOn_sphere_of_punctured {G V : ℂ → ℂ} {δ R : ℝ}
    (hR : 0 < R) (hRδ : R < δ)
    (heq : ∀ u : ℂ, 0 < ‖u‖ → ‖u‖ < δ → G u = V u) :
    Set.EqOn (logDeriv V) (logDeriv G) (Metric.sphere (0 : ℂ) R) := by
  intro z hz
  rw [Metric.mem_sphere, dist_zero_right] at hz
  have hz0 : 0 < ‖z‖ := by rw [hz]; exact hR
  have hzδ : ‖z‖ < δ := by rw [hz]; exact hRδ
  have hGVe : V =ᶠ[𝓝 z] G := by
    have h1 : {u : ℂ | 0 < ‖u‖} ∈ 𝓝 z := by
      have hset : {u : ℂ | 0 < ‖u‖} = ({0}ᶜ : Set ℂ) := by
        ext u; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff,
          norm_pos_iff]
      rw [hset]
      exact isOpen_compl_singleton.mem_nhds (norm_ne_zero_iff.mp hz0.ne')
    have h2 : Metric.ball (0 : ℂ) δ ∈ 𝓝 z :=
      Metric.isOpen_ball.mem_nhds (by rwa [Metric.mem_ball, dist_zero_right])
    filter_upwards [h1, h2] with u hu hu2
    have huδ : ‖u‖ < δ := by rwa [Metric.mem_ball, dist_zero_right] at hu2
    exact (heq u hu huδ).symm
  rw [logDeriv_apply, logDeriv_apply, hGVe.deriv_eq, ← heq z hz0 hzδ]

/-- The constant `2πi` is nonzero. -/
lemma two_pi_I_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
  exact_mod_cast Real.pi_ne_zero

theorem no_extension_of_logDeriv_period {V : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hV : ∀ u : ℂ, 0 < ‖u‖ → ‖u‖ < ρ → DifferentiableAt ℂ V u)
    (hper : ∀ r : ℝ, 0 < r → r < ρ →
      circleIntegral (logDeriv V) 0 r = 2 * Real.pi * Complex.I) :
    ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 →
      (∀ᶠ u : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ), G u = V u) → G 0 = 0 := by
  intro G hGan hGeq
  by_contra hne0
  obtain ⟨r₁, hr₁, hGan₁⟩ := hGan.exists_ball_analyticOnNhd
  obtain ⟨r₂, hr₂, hnv₂⟩ := exists_ball_ne_zero_of_continuousAt hGan.continuousAt hne0
  obtain ⟨δ, hδ, heqδ⟩ := exists_punctured_ball_eventuallyEq hGeq
  have hMpos : 0 < min (min ρ δ) (min r₁ r₂) := lt_min (lt_min hρ hδ) (lt_min hr₁ hr₂)
  set R : ℝ := min (min ρ δ) (min r₁ r₂) / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRM : R < min (min ρ δ) (min r₁ r₂) := by rw [hRdef]; linarith
  have hRρ : R < ρ := lt_of_lt_of_le hRM (le_trans (min_le_left _ _) (min_le_left _ _))
  have hRδ : R < δ := lt_of_lt_of_le hRM (le_trans (min_le_left _ _) (min_le_right _ _))
  have hRr : R < min r₁ r₂ := lt_of_lt_of_le hRM (min_le_right _ _)
  have hRr₁ : R < r₁ := lt_of_lt_of_le hRr (min_le_left _ _)
  have hGan' : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) (min r₁ r₂)) :=
    hGan₁.mono (Metric.ball_subset_ball (min_le_left _ _))
  have hnv' : ∀ z ∈ Metric.ball (0 : ℂ) (min r₁ r₂), G z ≠ 0 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact hnv₂ z (lt_of_lt_of_le hz (min_le_right _ _))
  have hzero : circleIntegral (logDeriv G) 0 R = 0 :=
    Commons.Analysis.Complex.circleIntegral_logDeriv_eq_zero_of_analyticOnNhd_ball
      hRpos hRr hGan' hnv'
  have hcongr : circleIntegral (logDeriv V) 0 R = circleIntegral (logDeriv G) 0 R :=
    circleIntegral.integral_congr hRpos.le
      (logDeriv_eqOn_sphere_of_punctured (G := G) (V := V) hRpos hRδ heqδ)
  exact two_pi_I_ne_zero (by rw [← hper R hRpos hRρ, hcongr, hzero])

end Work.Horn
