import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDzAux

open scoped Real Topology
open MeasureTheory Set Filter

theorem zmollKernel_hasDerivAt {H : ℝ → ℝ} (hH : MeasureTheory.LocallyIntegrable H MeasureTheory.volume)
    {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hM : ∀ x : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd δ x| ≤ M) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - t) * H t)
      (z⁻¹ * ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t) z := by
  -- The fixed interval `[a, b]` in the logarithmic variable on which the kernel lives.
  set a : ℝ := Real.log z - 2 with ha
  set b : ℝ := Real.log z + 2 with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (Real.log z))
  -- The window of `x` around `z` on which `log x - log z` varies by less than `1/2`.
  set s : Set ℝ := Set.Ioo (z / 2) (2 * z) with hs
  have hz2 : (0 : ℝ) < z / 2 := by linarith
  have hs_nhds : s ∈ 𝓝 z := by
    rw [hs]; exact Ioo_mem_nhds (by linarith) (by linarith)
  have hs_pos : ∀ x ∈ s, 0 < x := by
    intro x hx; rw [hs] at hx; linarith [hx.1, hz]
  have hlog2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    norm_num at h; exact h
  have hlog_lt : ∀ x ∈ s, Real.log x < Real.log z + 1 := by
    intro x hx
    have hx0 : 0 < x := hs_pos x hx
    have hlt : x < 2 * z := by rw [hs] at hx; exact hx.2
    have h1 : Real.log x < Real.log (2 * z) := Real.log_lt_log hx0 hlt
    have h2 : Real.log (2 * z) = Real.log 2 + Real.log z :=
      Real.log_mul (by norm_num) (ne_of_gt hz)
    linarith
  have hlog_gt : ∀ x ∈ s, Real.log z - 1 < Real.log x := by
    intro x hx
    have h1 : Real.log (z / 2) < Real.log x :=
      Real.log_lt_log hz2 (by rw [hs] at hx; exact hx.1)
    have h2 : Real.log (z / 2) = Real.log z - Real.log 2 :=
      Real.log_div (ne_of_gt hz) (by norm_num)
    linarith
  -- Vanishing of the two kernels far from the window.
  have hker_van : ∀ (x t : ℝ), x ∈ s → t ∉ Set.Ioc a b →
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log x - t) = 0 := by
    intro x t hx ht
    have hgt : Real.log z - 1 < Real.log x := hlog_gt x hx
    have hlt : Real.log x < Real.log z + 1 := hlog_lt x hx
    by_cases h : t ≤ a
    · have h2 : 1 ≤ Real.log x - t := by rw [ha] at h; linarith
      exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0
        (by rw [abs_of_nonneg (by linarith)]; linarith)
    · have hbt : b < t := by
        by_contra hc
        exact ht ⟨lt_of_not_ge h, le_of_not_gt hc⟩
      have h2 : 1 ≤ t - Real.log x := by rw [hb] at hbt; linarith
      exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0
        (by rw [abs_of_nonpos (by linarith)]; linarith)
  have hkerd_van : ∀ t : ℝ, t ∉ Set.Ioc a b →
      Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) = 0 := by
    intro t ht
    by_cases h : t ≤ a
    · have h2 : 1 < Real.log z - t := by rw [ha] at h; linarith
      exact sKerd_eq_zero_of_lt_abs hδ0
        (by rw [abs_of_nonneg (by linarith)]; linarith)
    · have hbt : b < t := by
        by_contra hc
        exact ht ⟨lt_of_not_ge h, le_of_not_gt hc⟩
      have h2 : 1 < t - Real.log z := by rw [hb] at hbt; linarith
      exact sKerd_eq_zero_of_lt_abs hδ0
        (by rw [abs_of_nonpos (by linarith)]; linarith)
  -- Interval integrability of the datum.
  have hsub : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hab]; exact fun t ht => ⟨le_of_lt ht.1, ht.2⟩
  have hF_int : IntervalIntegrable
      (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) * H t) volume a b := by
    rw [intervalIntegrable_iff]
    have hcont : ContinuousOn (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t))
        (Set.Icc a b) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous).comp
        (continuous_const.sub continuous_id)).continuousOn
    have hH_Icc : IntegrableOn H (Set.Icc a b) volume :=
      (hH.locallyIntegrableOn (Set.Icc a b)).integrableOn_isCompact isCompact_Icc
    have hprod : IntegrableOn
        (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) * H t)
        (Set.Icc a b) volume :=
      MeasureTheory.IntegrableOn.continuousOn_mul hcont hH_Icc isCompact_Icc
    exact hprod.mono_set hsub
  -- Interval integrability of the dominating function.
  have hbound_int : IntervalIntegrable (fun t : ℝ => M * (2 * z⁻¹) * |H t|) volume a b := by
    rw [intervalIntegrable_iff]
    have h1 : IntegrableOn (fun t : ℝ => M * (2 * z⁻¹) * |H t|) (Set.Icc a b) volume := by
      have h2 : IntegrableOn (fun t : ℝ => ‖H t‖) (Set.Icc a b) volume :=
        (hH.locallyIntegrableOn (Set.Icc a b)).norm.integrableOn_isCompact isCompact_Icc
      have h3 : Integrable (fun t : ℝ => M * (2 * z⁻¹) * |H t|)
          (volume.restrict (Set.Icc a b)) := by
        have h4 := h2.const_mul (M * (2 * z⁻¹))
        simpa [Real.norm_eq_abs] using h4
      exact h3
    exact h1.mono_set hsub
  -- The main differentiation under the integral sign.
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (x₀ := z)
    (F := fun x t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log x - t) * H t)
    (F' := fun x t : ℝ => (x⁻¹ * Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log x - t)) * H t)
    (bound := fun t : ℝ => M * (2 * z⁻¹) * |H t|)
    (s := s) hs_nhds
    (by
      refine Filter.Eventually.of_forall fun x => ?_
      have hcont : Continuous
          (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log x - t)) :=
        ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous).comp
          (continuous_const.sub continuous_id)
      exact hcont.aestronglyMeasurable.mul
        (hH.locallyIntegrableOn (Set.uIoc a b)).aestronglyMeasurable)
    hF_int
    (by
      have hcont : Continuous
          (fun t : ℝ => z⁻¹ * Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) :=
        continuous_const.mul ((continuous_sKerd δ).comp (continuous_const.sub continuous_id))
      exact hcont.aestronglyMeasurable.mul
        (hH.locallyIntegrableOn (Set.uIoc a b)).aestronglyMeasurable)
    (by
      refine Filter.Eventually.of_forall fun t _ x hx => ?_
      have hx0 : 0 < x := hs_pos x hx
      have hxinv : x⁻¹ ≤ 2 * z⁻¹ := by
        have h1 : (1 : ℝ) / x ≤ 1 / (z / 2) :=
          one_div_le_one_div_of_le hz2 (by rw [hs] at hx; linarith [hx.1])
        have h2 : (1 : ℝ) / (z / 2) = 2 * z⁻¹ := by rw [one_div, inv_div]; ring
        simpa [one_div, h2] using h1
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hx0)]
      calc x⁻¹ * |Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log x - t)| * |H t|
          ≤ (2 * z⁻¹) * M * |H t| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            exact mul_le_mul hxinv (hM _) (abs_nonneg _) (by positivity)
        _ = M * (2 * z⁻¹) * |H t| := by ring)
    hbound_int
    (by
      refine Filter.Eventually.of_forall fun t _ x hx => ?_
      have hx0 : 0 < x := hs_pos x hx
      have hker : HasDerivAt (fun y : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log y - t))
          (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log x - t) * x⁻¹) x := by
        have h1 : HasDerivAt (Work.FTS.EllSol.PkgK5.K5c.sKer δ)
            (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log x - t)) (Real.log x - t) := by
          simpa [Work.FTS.EllSol.EllPkgAux.sKerd] using
            (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).differentiable_one
              (Real.log x - t)).hasDerivAt)
        have h2 := h1.comp x ((Real.hasDerivAt_log (ne_of_gt hx0)).sub_const t)
        simpa [Function.comp_def] using h2
      have h3 := hker.mul_const (H t)
      refine h3.congr_deriv ?_
      ring)
  -- Transfer to the integral over `ℝ`.
  have key2 : HasDerivAt (fun x : ℝ => ∫ t : ℝ,
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log x - t) * H t)
      (∫ t in a..b, (z⁻¹ * Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) * H t) z := by
    refine (Filter.EventuallyEq.hasDerivAt_iff ?_).mpr key.2
    filter_upwards [hs_nhds] with x hx
    rw [intervalIntegral.integral_of_le hab]
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro t ht
    rw [hker_van x t hx ht, zero_mul]
  -- Identification of the derivative.
  have hval : (∫ t in a..b,
        (z⁻¹ * Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) * H t)
      = z⁻¹ * ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t := by
    have s1 : (∫ t in a..b,
          (z⁻¹ * Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) * H t)
        = ∫ t in a..b,
            z⁻¹ * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t) := by
      refine intervalIntegral.integral_congr ?_
      intro t _
      ring
    have s2 : (∫ t in a..b,
          z⁻¹ * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t))
        = z⁻¹ * ∫ t in a..b, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t :=
      intervalIntegral.integral_const_mul z⁻¹ _
    have s3 : (∫ t in a..b, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t)
        = ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t := by
      rw [intervalIntegral.integral_of_le hab]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht => by rw [hkerd_van t ht, zero_mul])
    rw [s1, s2, s3]
  exact key2.congr_deriv hval

end Work.FTS.EllSol.EllPkgAux.MollDzAux
