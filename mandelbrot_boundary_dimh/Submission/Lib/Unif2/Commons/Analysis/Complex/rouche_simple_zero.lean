import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.divisor_subBall_factor
import Submission.Lib.Unif2.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_annulus_lt_of_lt_on_sphere
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleIntegral_logDeriv_add_eq
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_unique_zero_of_divisor_finsum_eq_one
import Submission.Lib.Unif2.Commons.Analysis.Complex.circleIntegral_logDeriv_eq_divisor

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Real Interval Topology BigOperators

namespace Commons.Analysis.Complex




/-- The divisor over a ball of a function analytic on a larger ball has finite support. -/
lemma divisor_support_finite_of_analyticOnNhd_ball {R ρ : ℝ} (hρR : ρ < R) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball (0:ℂ) R)) :
    (MeromorphicOn.divisor h (Metric.ball (0:ℂ) ρ)).support.Finite := by
  have hmer : MeromorphicOn h (Metric.closedBall (0:ℂ) ρ) := by
    intro z hz
    exact (hh z (Metric.closedBall_subset_ball hρR hz)).meromorphicAt
  exact MeromorphicOn.divisor_ball_support_finite hmer

/-- Casting an integer-valued finsum into `ℂ` is the same as the `ℂ`-valued finsum. -/
lemma finsum_int_cast_finsum {d : ℂ → ℤ} (hd : HasFiniteSupport d) :
    (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ)) = (((∑ᶠ u : ℂ, d u) : ℤ) : ℂ) :=
  (map_finsum (Int.castAddHom ℂ) hd).symm

theorem divisor_finsum_eq_one_of_unique_simple_zero {R ρ : ℝ} (_hρ : 0 < ρ) (hρR : ρ < R)
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball (0:ℂ) R))
    (ha : a ∈ Metric.ball (0:ℂ) ρ) (hfa : f a = 0) (hder : deriv f a ≠ 0)
    (honly : ∀ z ∈ Metric.ball (0:ℂ) ρ, f z = 0 → z = a) :
    (∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ)) u : ℤ)) = 1 := by
  have hfρ : AnalyticOnNhd ℂ f (Metric.ball (0:ℂ) ρ) :=
    hf.mono (Metric.ball_subset_ball hρR.le)
  have hdiv_a : (MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ)) a = 1 := by
    rw [AnalyticOnNhd.divisor_apply hfρ ha]
    have hord : analyticOrderAt f a = 1 :=
      (hfρ a ha).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfa hder
    simp [hord]
  have hdiv_other : ∀ b, b ≠ a → (MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ)) b = 0 := by
    intro b hb
    by_cases hbm : b ∈ Metric.ball (0:ℂ) ρ
    · rw [AnalyticOnNhd.divisor_apply hfρ hbm]
      have hfb : f b ≠ 0 := fun h0 => hb (honly b hbm h0)
      have hz : analyticOrderAt f b = 0 := (hfρ b hbm).analyticOrderAt_eq_zero.mpr hfb
      simp [hz]
    · rw [MeromorphicOn.divisor_def]
      simp [hbm]
  rw [finsum_eq_single _ a hdiv_other, hdiv_a]

theorem rouche_simple_zero {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ} {a : ℂ} (ha : ‖a‖ < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0:ℂ) R)) (hfc : ContinuousOn f (Metric.closedBall (0:ℂ) R))
    (hg : DifferentiableOn ℂ g (Metric.closedBall (0:ℂ) R)) (hgc : ContinuousOn g (Metric.closedBall (0:ℂ) R))
    (h : ∀ z ∈ Metric.sphere (0:ℂ) R, ‖g z‖ < ‖f z‖)
    (hf1 : f a = 0) (hder : deriv f a ≠ 0)
    (hfonly : ∀ z ∈ Metric.ball (0:ℂ) R, f z = 0 → z = a) :
    ∃ z ∈ Metric.ball (0:ℂ) R, (f z + g z = 0) ∧
      (∀ y ∈ Metric.ball (0:ℂ) R, f y + g y = 0 → y = z) := by
  obtain ⟨ρ, hρpos, hρR, hann⟩ := exists_annulus_lt_of_lt_on_sphere hR hfc hgc h
  have hf_an : AnalyticOnNhd ℂ f (Metric.ball (0:ℂ) R) :=
    (hf.mono Metric.ball_subset_closedBall).analyticOnNhd Metric.isOpen_ball
  have hg_an : AnalyticOnNhd ℂ g (Metric.ball (0:ℂ) R) :=
    (hg.mono Metric.ball_subset_closedBall).analyticOnNhd Metric.isOpen_ball
  have hfg_an : AnalyticOnNhd ℂ (fun w => f w + g w) (Metric.ball (0:ℂ) R) :=
    hf_an.add hg_an
  have ha_ball : a ∈ Metric.ball (0:ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]
    by_contra hlt
    rw [not_lt] at hlt
    have h1 := hann a hlt ha.le
    rw [hf1, norm_zero] at h1
    linarith [norm_nonneg (g a)]
  have hf_ne : ∀ z ∈ Metric.sphere (0:ℂ) ρ, f z ≠ 0 := by
    intro z hz h0
    have hzρ : ρ ≤ ‖z‖ := by
      have h' := mem_sphere_iff_norm.mp hz
      rw [sub_zero] at h'
      linarith [h'.ge]
    have hzR : ‖z‖ ≤ R := by
      have h' := mem_sphere_iff_norm.mp hz
      rw [sub_zero] at h'
      linarith [h'.le]
    have h1 := hann z hzρ hzR
    rw [h0, norm_zero] at h1
    linarith [norm_nonneg (g z)]
  have hlt_sphere : ∀ z ∈ Metric.sphere (0:ℂ) ρ, ‖g z‖ < ‖f z‖ := by
    intro z hz
    have hzρ : ρ ≤ ‖z‖ := by
      have h' := mem_sphere_iff_norm.mp hz
      rw [sub_zero] at h'
      linarith [h'.ge]
    have hzR : ‖z‖ ≤ R := by
      have h' := mem_sphere_iff_norm.mp hz
      rw [sub_zero] at h'
      linarith [h'.le]
    exact hann z hzρ hzR
  have hfg_ne : ∀ z ∈ Metric.sphere (0:ℂ) ρ, (fun w => f w + g w) z ≠ 0 := by
    intro z hz h0
    change f z + g z = 0 at h0
    have hlt := hlt_sphere z hz
    have hb : ‖f z‖ ≤ ‖f z + g z‖ + ‖g z‖ := by
      have := norm_add_le (f z + g z) (-(g z))
      simpa using this
    rw [h0, norm_zero, zero_add] at hb
    linarith
  have hf_int := circleIntegral_logDeriv_eq_divisor hρpos hρR hf_an hf_ne
  have hfg_int := circleIntegral_logDeriv_eq_divisor hρpos hρR hfg_an hfg_ne
  have hlog := circleIntegral_logDeriv_add_eq hρpos hρR hf_an hg_an hf_ne hlt_sphere
  have hNf : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ)) u : ℤ)) = 1 :=
    divisor_finsum_eq_one_of_unique_simple_zero hρpos hρR hf_an ha_ball hf1 hder
      (fun z hz hz0 => hfonly z (Metric.ball_subset_ball hρR.le hz) hz0)
  have hf_fin : HasFiniteSupport (fun u : ℂ => ((MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ)) u : ℤ)) :=
    divisor_support_finite_of_analyticOnNhd_ball hρR hf_an
  have hfg_fin : HasFiniteSupport (fun u : ℂ =>
      ((MeromorphicOn.divisor (fun w => f w + g w) (Metric.ball (0:ℂ) ρ)) u : ℤ)) :=
    divisor_support_finite_of_analyticOnNhd_ball hρR hfg_an
  have hNh : (∑ᶠ u : ℂ,
      ((MeromorphicOn.divisor (fun w => f w + g w) (Metric.ball (0:ℂ) ρ)) u : ℤ)) = 1 := by
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
      exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hA_eq_B : (∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (fun w => f w + g w) (Metric.ball (0:ℂ) ρ)) u : ℤ) : ℂ))
        = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.ball (0:ℂ) ρ)) u : ℤ) : ℂ)) :=
      mul_left_cancel₀ h2pi (hfg_int.symm.trans (hlog.trans hf_int))
    have hA_one : (∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (fun w => f w + g w) (Metric.ball (0:ℂ) ρ)) u : ℤ) : ℂ)) = 1 := by
      rw [hA_eq_B, finsum_int_cast_finsum hf_fin, hNf]
      norm_num
    have hcast : (((∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor (fun w => f w + g w) (Metric.ball (0:ℂ) ρ)) u : ℤ)) : ℤ) : ℂ)
        = ((1 : ℤ) : ℂ) := by
      rw [← finsum_int_cast_finsum hfg_fin]
      simpa using hA_one
    exact Int.cast_injective hcast
  obtain ⟨z, hz_ball, hz0, hzuniq⟩ := exists_unique_zero_of_divisor_finsum_eq_one hρpos hρR.le hfg_an hNh
  refine ⟨z, Metric.ball_subset_ball hρR.le hz_ball, hz0, ?_⟩
  intro y hy hy0
  apply hzuniq y ?_ hy0
  by_contra hyr
  rw [Metric.mem_ball, dist_zero_right] at hyr
  rw [not_lt] at hyr
  have hylt : ‖y‖ < R := by
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hy
  have h1 := hann y hyr hylt.le
  have hfe : f y = -g y := by linear_combination hy0
  rw [hfe] at h1
  simp at h1

end Commons.Analysis.Complex
