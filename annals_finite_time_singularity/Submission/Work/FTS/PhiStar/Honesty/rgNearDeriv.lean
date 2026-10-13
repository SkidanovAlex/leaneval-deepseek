import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.rgNearSetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist

set_option autoImplicit false

set_option maxHeartbeats 1000000

lemma radGreen_deriv_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → 2 * z ≤ δ →
      ‖deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z‖
        ≤ rgA1 α m * ε * z ^ ((1 : ℝ) / 2) + rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1) := by
  intro z hz0 h2z
  have hK : 0 < rgK α m := rgK_pos hα m
  have hp : 0 < rgP α m := rgP_pos hα hm
  have hcfg : 0 ≤ rgCF α m c δ := rgCF_nonneg (α := α) (m := m) (c := c) hδ
  set L : ℝ := rgA1 α m * ε * z ^ ((1 : ℝ) / 2)
    + rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1) with hLdef
  have hA1pos : 0 < rgA1 α m := by
    rw [rgA1]
    have hq : 0 < rgQ α m := rgQ_pos hα m
    have hp3 : 0 < rgP α m - 3 / 2 := by have := rgP_ge hα hα4 hm; linarith
    have ha : (0 : ℝ) < rgQ α m * 2 ^ (rgQ α m + 3 / 2) / (rgQ α m + 3 / 2) :=
      div_pos (mul_pos hq (Real.rpow_pos_of_pos (by norm_num) _)) (by linarith)
    have hb : (0 : ℝ) < 2 ^ (rgQ α m + 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hc : (0 : ℝ) < rgP α m * 2 ^ (rgP α m - 1) / (rgP α m - 3 / 2) :=
      div_pos (mul_pos hp (Real.rpow_pos_of_pos (by norm_num) _)) hp3
    exact mul_pos hK (add_pos (add_pos (add_pos ha hb) hc) one_pos)
  have hA2nn : 0 ≤ rgA2 α m * rgCF α m c δ * z ^ (rgP α m - 1) := by
    have h2 : 0 ≤ rgA2 α m := by
      rw [rgA2]
      exact mul_nonneg hK.le (mul_nonneg hp.le (Real.rpow_pos_of_pos (by norm_num) _).le)
    exact mul_nonneg (mul_nonneg h2 hcfg) (Real.rpow_nonneg hz0.le _)
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    exact add_nonneg (mul_nonneg (mul_nonneg hA1pos.le hε) (Real.rpow_nonneg hz0.le _)) hA2nn
  rw [hLdef] at hLnn
  obtain ⟨c₀, h₀, hh₀, hstep, hc₀⟩ :=
    radGreen_step_decomp (m := m) (c := c) hα hα4 hm hδ hδ1 hε hvy hnear hfar z hz0 h2z
  have hsmall : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), h ≤ h₀ :=
    mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds hh₀)) (fun h hh => (le_of_lt hh : h ≤ h₀))
  rcases eq_or_ne c₀ 0 with hzero | hne
  · have hin : ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ‖Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
          - Work.FTS.PhiStar.Radial.radGreen α m c z‖ ≤ L * h := by
      intro h hh hle
      simpa only [hLdef, hzero, sub_zero] using hstep h hh hle
    by_cases hd : DifferentiableAt ℝ (Work.FTS.PhiStar.Radial.radGreen α m c) z
    · have hslope : Tendsto (fun h : ℝ => h⁻¹ • (Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
            - Work.FTS.PhiStar.Radial.radGreen α m c z))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z)) :=
        (hd.hasDerivAt.tendsto_slope_zero).mono_left
          (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
      refine le_of_tendsto hslope.norm ?_
      filter_upwards [hsmall, self_mem_nhdsWithin] with h hle hh
      have hpos : 0 < h := hh
      have hinv : 0 ≤ h⁻¹ := inv_nonneg.mpr hpos.le
      calc ‖h⁻¹ • (Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
              - Work.FTS.PhiStar.Radial.radGreen α m c z)‖
          = h⁻¹ * ‖Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
              - Work.FTS.PhiStar.Radial.radGreen α m c z‖ := by
            rw [smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
        _ ≤ h⁻¹ * (L * h) := mul_le_mul_of_nonneg_left (hin h hpos hle) hinv
        _ = L := by field_simp
    · rw [hLdef, deriv_zero_of_not_differentiableAt hd]
      simpa using hLnn
  · set m₀ : ℝ := min h₀ (‖c₀‖ / (2 * (L + 1))) with hm₀def
    have hm₀pos : 0 < m₀ := lt_min hh₀ (by positivity)
    have hjump : ∀ h : ℝ, 0 < h → h ≤ m₀ →
        ‖c₀‖ / 2 ≤ ‖Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
          - Work.FTS.PhiStar.Radial.radGreen α m c z‖ := by
      intro h hpos hle
      have hb := hstep h hpos (le_trans hle (min_le_left _ _))
      have hh2 : h ≤ ‖c₀‖ / (2 * (L + 1)) := le_trans hle (min_le_right _ _)
      have h2 : ‖c₀‖ - ‖Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
            - Work.FTS.PhiStar.Radial.radGreen α m c z - c₀‖
          ≤ ‖Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
            - Work.FTS.PhiStar.Radial.radGreen α m c z‖ := by
        have hkey : c₀ = (Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
            - Work.FTS.PhiStar.Radial.radGreen α m c z)
            - (Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
              - Work.FTS.PhiStar.Radial.radGreen α m c z - c₀) := by ring
        have h3 := norm_sub_le (Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
          - Work.FTS.PhiStar.Radial.radGreen α m c z)
          (Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
            - Work.FTS.PhiStar.Radial.radGreen α m c z - c₀)
        rw [← hkey] at h3
        linarith
      have h3 : L * h ≤ ‖c₀‖ / 2 := by
        have hA : h * (2 * (L + 1)) ≤ ‖c₀‖ := by
          have hh := mul_le_mul_of_nonneg_right hh2 (by linarith : (0 : ℝ) ≤ 2 * (L + 1))
          rwa [div_mul_cancel₀ _ (by linarith : (2 * (L + 1)) ≠ 0)] at hh
        have hB : 2 * (L * h) ≤ h * (2 * (L + 1)) := by nlinarith [hpos, hLnn]
        linarith
      linarith
    have hnotdiff : ¬ DifferentiableAt ℝ (Work.FTS.PhiStar.Radial.radGreen α m c) z := by
      intro hd
      have hcont : ContinuousAt (Work.FTS.PhiStar.Radial.radGreen α m c) z := hd.continuousAt
      have h1 : Tendsto (fun h : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c (z + h))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Work.FTS.PhiStar.Radial.radGreen α m c z)) := by
        have hthis : Tendsto (fun h : ℝ => z + h) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (z + 0)) :=
          ((tendsto_const_nhds.add tendsto_id) : Tendsto (fun h : ℝ => z + h) (nhds (0:ℝ))
            (nhds (z + 0))).mono_left nhdsWithin_le_nhds
        exact hcont.tendsto.comp (by simpa using hthis)
      have h2 : Tendsto (fun h : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
            - Work.FTS.PhiStar.Radial.radGreen α m c z)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have hz' : Tendsto (fun _ : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (Work.FTS.PhiStar.Radial.radGreen α m c z)) := tendsto_const_nhds
        have := h1.sub hz'
        simpa using this
      have h3 : Tendsto (fun h : ℝ => ‖Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
            - Work.FTS.PhiStar.Radial.radGreen α m c z‖)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using h2.norm
      have h4 : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ‖c₀‖ / 2 ≤ ‖Work.FTS.PhiStar.Radial.radGreen α m c (z + h)
            - Work.FTS.PhiStar.Radial.radGreen α m c z‖ := by
        filter_upwards [mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds hm₀pos))
            (fun h hh => (le_of_lt hh : h ≤ m₀)), self_mem_nhdsWithin] with h hle hh
        exact hjump h hh hle
      have hle0 := le_of_tendsto_of_tendsto tendsto_const_nhds h3 h4
      have hne2 : 0 < ‖c₀‖ / 2 := by
        have : 0 < ‖c₀‖ := abs_pos.mpr hne
        linarith
      linarith
    rw [hLdef, deriv_zero_of_not_differentiableAt hnotdiff]
    simpa using hLnn

end Work.FTS.PhiStar.Honesty
