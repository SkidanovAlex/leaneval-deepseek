import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.Defs

/-!
# `∫ ∂̄G = 0` for compactly supported `G`

The two-dimensional case of "a compactly supported exact form integrates to zero": for
`G : ℂ → ℂ` of class `C¹` with compact support the integral of `∂̄G = ∂_x G + i ∂_y G` vanishes.

The proof avoids Fubini/co-ordinate bookkeeping.  For a fixed direction `v`, the function
`Φ t = ∫ z, G (z + t • v)` is *constant* by translation invariance of Lebesgue measure, hence
`Φ'(0) = 0`; differentiating under the integral sign (parametric integral with an explicit
integrable bound coming from compact support) identifies `Φ'(0)` with `∫ z, ∂_v G z`.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- For `G : ℂ → ℂ` of class `C¹` with compact support and any direction `v`, the integral of the
directional derivative `∂_v G` vanishes. -/
theorem integral_fderiv_eq_zero (G : ℂ → ℂ) (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G)
    (v : ℂ) : ∫ z, fderiv ℝ G z v ∂volume = 0 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  obtain ⟨R₀, hR₀⟩ := hc.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 with hRdef
  have hR : tsupport G ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hzero' : ∀ z : ℂ, R < ‖z‖ → fderiv ℝ G z = 0 := by
    intro z hz
    have hopen : IsOpen {z' : ℂ | R < ‖z'‖} := isOpen_lt continuous_const continuous_norm
    have hev : G =ᶠ[𝓝 z] 0 := by
      filter_upwards [hopen.mem_nhds hz] with z' hz'
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have h := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact absurd h (not_le_of_gt hz')
    rw [hev.fderiv_eq]; simp
  have hcontv : Continuous fun z : ℂ => fderiv ℝ G z v :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z : ℂ, ‖fderiv ℝ G z v‖ ≤ M := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      hcontv.continuousOn
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : ‖z‖ ≤ R
    · refine le_trans (hC z ?_) (le_max_left _ _)
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    · rw [hzero' z (not_le.mp hz)]
      simp only [ContinuousLinearMap.zero_apply, norm_zero]
      exact le_max_right _ _
  have hbound_int : Integrable (fun z : ℂ =>
      M * (Metric.closedBall 0 (R + ‖v‖ + 1)).indicator (fun _ => (1 : ℝ)) z) volume := by
    refine Integrable.const_mul ?_ M
    rw [integrable_indicator_iff (isCompact_closedBall (0 : ℂ) (R + ‖v‖ + 1)).measurableSet]
    exact integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne (by simp)
  have hdom : ∀ z : ℂ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      ‖fderiv ℝ G (z + t • v) v‖ ≤
        M * (Metric.closedBall 0 (R + ‖v‖ + 1)).indicator (fun _ => (1 : ℝ)) z := by
    intro z t ht
    by_cases hz : ‖z‖ ≤ R + ‖v‖ + 1
    · have hzK : z ∈ Metric.closedBall (0 : ℂ) (R + ‖v‖ + 1) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
      rw [Set.indicator_of_mem hzK, mul_one]
      exact hM _
    · have hzbig : R < ‖z + t • v‖ := by
        have h1 : ‖z‖ - ‖t • v‖ ≤ ‖z + t • v‖ := by
          have hthis : |‖z‖ - ‖t • v‖| ≤ ‖z + t • v‖ := by
            have h0 := abs_norm_sub_norm_le z (-(t • v))
            rwa [show z - -(t • v) = z + t • v by abel, norm_neg] at h0
          exact le_trans (le_abs_self _) hthis
        have h2 : ‖t • v‖ = |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
        rw [h2] at h1
        have ht1 : |t| < 1 := abs_lt.mpr ht
        have h4 : |t| * ‖v‖ < ‖v‖ := by
          simpa using mul_lt_mul_of_pos_right ht1 (norm_pos_iff.mpr hv)
        have h3 : R + ‖v‖ + 1 < ‖z‖ := not_le.mp hz
        linarith
      have h3 : fderiv ℝ G (z + t • v) = 0 := hzero' _ hzbig
      rw [h3]
      simp only [ContinuousLinearMap.zero_apply, norm_zero]
      exact mul_nonneg (le_trans (norm_nonneg _) (hM 0))
        (Set.indicator_nonneg (fun _ _ => by norm_num) z)
  have hconst : ∀ t : ℝ, (∫ z, G (z + t • v) ∂volume) = ∫ z, G z ∂volume :=
    fun t => integral_add_right_eq_self G (t • v)
  have hGint : Integrable G volume := hG.continuous.integrable_of_hasCompactSupport hc
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (s := Set.Ioo (-1 : ℝ) 1) (x₀ := 0)
    (bound := fun z : ℂ => M * (Metric.closedBall 0 (R + ‖v‖ + 1)).indicator (fun _ => (1 : ℝ)) z)
    (F := fun t z => G (z + t • v)) (F' := fun t z => fderiv ℝ G (z + t • v) v)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t =>
      (hG.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (by simpa using hGint)
    (by simpa using hcontv.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => hdom z)
    hbound_int
    (Filter.Eventually.of_forall fun z => fun t _ => by
      have hcurve : HasDerivAt (fun s : ℝ => z + s • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add z
      exact ((hG.differentiable one_ne_zero) (z + t • v)).hasFDerivAt.comp_hasDerivAt t hcurve)
  have hderiv0 : HasDerivAt (fun t : ℝ => ∫ z, G (z + t • v) ∂volume) 0 0 := by
    have : (fun t : ℝ => ∫ z, G (z + t • v) ∂volume) = fun _ => ∫ z, G z ∂volume :=
      funext hconst
    rw [this]
    exact hasDerivAt_const 0 _
  have := hderiv0.unique hmain.2
  simpa using this.symm

/-- For a `C¹` function with compact support the integral of `∂̄G = ∂_x G + i ∂_y G` vanishes. -/
theorem integral_dbar_eq_zero (G : ℂ → ℂ) (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G) :
    ∫ z, dbar G z ∂volume = 0 := by
  obtain ⟨R₀, hR₀⟩ := hc.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 with hRdef
  have hR : tsupport G ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hzero' : ∀ z : ℂ, R < ‖z‖ → fderiv ℝ G z = 0 := by
    intro z hz
    have hopen : IsOpen {z' : ℂ | R < ‖z'‖} := isOpen_lt continuous_const continuous_norm
    have hev : G =ᶠ[𝓝 z] 0 := by
      filter_upwards [hopen.mem_nhds hz] with z' hz'
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have h := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact absurd h (not_le_of_gt hz')
    rw [hev.fderiv_eq]; simp
  have hcs : ∀ vec : ℂ, HasCompactSupport fun z : ℂ => fderiv ℝ G z vec := by
    intro vec
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R) ?_
    intro z hz
    simp only [Function.mem_support] at hz
    by_contra hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hz (by rw [hzero' z (not_le.mp hmem)]; simp)
  have hint1 : Integrable (fun z : ℂ => fderiv ℝ G z 1) volume :=
    Continuous.integrable_of_hasCompactSupport
      ((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hcs 1)
  have hint2 : Integrable (fun z : ℂ => fderiv ℝ G z Complex.I) volume :=
    Continuous.integrable_of_hasCompactSupport
      ((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hcs Complex.I)
  have key1 := integral_fderiv_eq_zero G hG hc 1
  have key2 := integral_fderiv_eq_zero G hG hc Complex.I
  have hfun : (fun z : ℂ => dbar G z)
      = fun z => fderiv ℝ G z 1 + Complex.I * fderiv ℝ G z Complex.I := by
    funext z; rfl
  have hdecomp : ∫ z, dbar G z ∂volume
      = (∫ z, fderiv ℝ G z 1 ∂volume) + Complex.I * ∫ z, fderiv ℝ G z Complex.I ∂volume := by
    rw [hfun, integral_add hint1 (hint2.const_mul Complex.I), integral_const_mul]
  rw [hdecomp, key1, key2]
  simp

end Work.Analysis.Complex.DbarCauchy

end
