import Mathlib
import Submission.Work.Smooth.JordanSeparation.WeakDefs
import Submission.Work.Smooth.JordanSeparation.DenomWeak
import Submission.Work.Smooth.JordanSeparation.ModelWeak
import Submission.Work.Smooth.JordanSeparation.tendsto_winding_jump_integral
import Submission.Work.Smooth.JordanSeparation.deriv_uniform_continuous
import Submission.Work.Smooth.JordanSeparation.far_chord_bound

/-!
# The winding-jump integral tends to `π·conj(unitTangent c 0)` at a regular parameter

`tendsto_winding_jump_integral` of the sibling file, with the hypothesis `deriv c.γ 0 ≠ 0` in place
of `c.IsImmersion` (the proof uses the immersion only at the parameter `0`, for the denominator
estimate and for the local linearisation, and uses only the *upper* bound on `‖γ'‖`).
-/

open Set Filter
open scoped Topology
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

theorem continuous_jwModel_of_deriv_ne_zero (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) {s : ℝ} (hs : 0 < s) :
    Continuous (jwModel c s) := by
  have hu : unitTangent c 0 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_unitTangent_of_deriv_ne_zero c hreg]; norm_num
  have hne : ∀ τ : ℝ, (deriv c.γ 0) ^ 2 * (τ : ℂ) ^ 2
      + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2 ≠ 0 := by
    intro τ
    rw [jwModel_denom_factor c hreg τ s]
    refine mul_ne_zero (pow_ne_zero 2 hu) ?_
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hden : Continuous fun τ : ℝ =>
      (deriv c.γ 0) ^ 2 * (τ : ℂ) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2 :=
    ((continuous_const.mul (Complex.continuous_ofReal.pow 2)).add continuous_const)
  exact continuous_const.div hden hne

/-- **The winding-jump integral tends to `π·conj(unitTangent c 0)`.** -/
theorem tendsto_winding_jump_integral_of_deriv_ne_zero (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (hreg : deriv c.γ 0 ≠ 0) (hsimple : c.toPlaneCurve.IsSimple) :
    Filter.Tendsto (fun s : ℝ => ∫ τ in (0 : ℝ)..(2 * Real.pi),
        (s * deriv c.γ τ) /
          ((c.γ τ - c.γ 0) ^ 2
            + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((Real.pi : ℂ) * (starRingEnd ℂ) (Work.Smooth.JordanSeparation.unitTangent c 0))) := by
  rw [Metric.tendsto_nhds]
  intro δ' hδ'
  have hρ : 0 < ‖deriv c.γ 0‖ := norm_pos_iff.mpr hreg
  set A : ℝ := ‖deriv c.γ 0‖ ^ 2 / 2 with hAdef
  have hA : 0 < A := by rw [hAdef]; positivity
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  set C : ℝ := 4 * Real.pi / Real.sqrt A + 3 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  -- the master estimate, for every smallness parameter `η`
  have key : ∀ η : ℝ, 0 < η → η ≤ ‖deriv c.γ 0‖ / 8 → η ≤ 1 →
      ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖(∫ τ in (0 : ℝ)..(2 * Real.pi), jwIntegrand c s τ)
            - (Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖ ≤ C * η := by
    intro η hη hη8 hη1
    -- linearisation data at `τ = 0`
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := deriv_uniform_continuous c η hη
    have hexp : ∀ τ : ℝ, |τ| ≤ δ₁ →
        ‖(c.γ τ - c.γ 0) - (τ : ℂ) * deriv c.γ 0‖ ≤ η * |τ| := by
      intro τ hτ
      have hC1 : ∀ x : ℝ, |x - 0| ≤ δ₁ → ‖deriv c.γ x - deriv c.γ 0‖ ≤ η := by
        intro x hx; simpa using hδ₁ x 0 hx
      have hres := norm_chord_sub_deriv_mul_le c (t := 0) (t' := τ) (C := η) hC1
        (by simpa using hτ)
      simpa using hres
    have hder : ∀ τ : ℝ, |τ| ≤ δ₁ → ‖deriv c.γ τ - deriv c.γ 0‖ ≤ η :=
      fun τ hτ => by simpa using hδ₁ τ 0 (by simpa using hτ)
    obtain ⟨δc, hδcpos, hδc⟩ := exists_denom_ne_zero_of_deriv_ne_zero c hreg hsimple
    have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    -- the split point
    set ε : ℝ := min δ₁ 1 with hεdef
    have hεpos : 0 < ε := lt_min hδ₁pos one_pos
    have hεδ : ε ≤ δ₁ := min_le_left _ _
    have hε1 : ε ≤ 1 := min_le_right _ _
    have hεpi : ε ≤ Real.pi := by linarith
    have hε2π : ε ≤ 2 * Real.pi - ε := by linarith
    obtain ⟨mc, hmcpos, hmc⟩ := far_chord_bound c hsimple hεpos hεpi
    obtain ⟨M₁, hM₁, hM₁up⟩ := deriv_global_norm_upper c
    -- the threshold below which `s` is controlled
    set δs : ℝ := min (min δc (mc / 2)) (η * mc ^ 2 / (8 * M₁ * Real.pi + 1)) with hδsdef
    have hδspos : 0 < δs := by
      rw [hδsdef]
      exact lt_min (lt_min hδcpos (by positivity)) (by positivity)
    -- the limit of the model integral
    have hE1 := tendsto_model_integral_of_deriv_ne_zero c hreg hεpos
    have hE1' : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        dist (∫ τ in (0 : ℝ)..ε, jwModel c s τ)
          ((Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0)) < η :=
      Metric.tendsto_nhds.mp hE1 η hη
    have hEs : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), s ∈ Set.Ioo 0 δs := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_Iio.mem_nhds (show (0 : ℝ) < δs from hδspos)] with s hlt hpos
      exact ⟨hpos, hlt⟩
    filter_upwards [hE1', hEs] with s hE1s hsIoo
    have hs : 0 < s := hsIoo.1
    have hsδc : s < δc :=
      lt_of_lt_of_le (lt_of_lt_of_le hsIoo.2 (min_le_left _ _)) (min_le_left _ _)
    have hsmc : s < mc / 2 :=
      lt_of_lt_of_le (lt_of_lt_of_le hsIoo.2 (min_le_left _ _)) (min_le_right _ _)
    have hsη : s * (8 * M₁ * Real.pi + 1) < η * mc ^ 2 := by
      have hlt := lt_of_lt_of_le hsIoo.2 (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at hlt
      linarith
    have hne : ∀ τ : ℝ, (c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2 ≠ 0 :=
      hδc s hs hsδc
    have hcontf : Continuous (jwIntegrand c s) := continuous_jwIntegrand c hne
    have hcontg : Continuous (jwModel c s) := continuous_jwModel_of_deriv_ne_zero c hreg hs
    have hu : ‖unitTangent c 0‖ = 1 := norm_unitTangent_of_deriv_ne_zero c hreg
    have hE1s' : ‖(∫ τ in (0 : ℝ)..ε, jwModel c s τ)
        - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖ ≤ η := by
      rw [← dist_eq_norm]; exact le_of_lt hE1s
    -- the pointwise comparison with the model
    have hpoint : ∀ τ : ℝ, |τ| ≤ ε →
        ‖jwIntegrand c s τ - jwModel c s τ‖ ≤ 4 * η * (s / (A * τ ^ 2 + s ^ 2)) := by
      intro τ hτ
      have hτδ : |τ| ≤ δ₁ := le_trans hτ hεδ
      have hb := norm_integrand_sub_model_le_of_deriv_ne_zero c hreg hη.le hη8 (hexp τ hτδ) (hder τ hτδ) (hne τ) hs
      rw [← hAdef] at hb
      rw [show 4 * η * s / (A * τ ^ 2 + s ^ 2) = 4 * η * (s / (A * τ ^ 2 + s ^ 2))
        from by rw [mul_div_assoc]] at hb
      exact hb
    have hboundfun_cont : Continuous fun τ : ℝ => 4 * η * (s / (A * τ ^ 2 + s ^ 2)) := by
      refine continuous_const.mul (continuous_const.div ?_ ?_)
      · exact (continuous_const.mul (continuous_pow 2)).add continuous_const
      · intro x; positivity
    have hmodel_bound : (4 * η) * ((Real.pi / 2) / Real.sqrt A)
        = 2 * Real.pi * η / Real.sqrt A := by
      have hne0 : Real.sqrt A ≠ 0 := ne_of_gt hsqrtA
      rw [eq_div_iff hne0]
      field_simp
      ring
    -- the piece `[0, ε]`
    have hP1 : ‖(∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
        - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖
        ≤ 2 * Real.pi * η / Real.sqrt A + η := by
      have hsub : ∫ τ in (0 : ℝ)..ε, (jwIntegrand c s τ - jwModel c s τ)
          = (∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
            - (∫ τ in (0 : ℝ)..ε, jwModel c s τ) :=
        intervalIntegral.integral_sub (hcontf.intervalIntegrable _ _)
          (hcontg.intervalIntegrable _ _)
      have hbnd : ∫ τ in (0 : ℝ)..ε, ‖jwIntegrand c s τ - jwModel c s τ‖
          ≤ 2 * Real.pi * η / Real.sqrt A := by
        calc ∫ τ in (0 : ℝ)..ε, ‖jwIntegrand c s τ - jwModel c s τ‖
            ≤ ∫ τ in (0 : ℝ)..ε, 4 * η * (s / (A * τ ^ 2 + s ^ 2)) := by
              refine intervalIntegral.integral_mono_on hεpos.le ?_ ?_ ?_
              · exact (hcontf.sub hcontg).norm.intervalIntegrable _ _
              · exact hboundfun_cont.intervalIntegrable _ _
              · intro x hx
                exact hpoint x (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          _ = (4 * η) * ∫ τ in (0 : ℝ)..ε, s / (A * τ ^ 2 + s ^ 2) :=
              intervalIntegral.integral_const_mul _ _
          _ ≤ (4 * η) * ((Real.pi / 2) / Real.sqrt A) :=
              mul_le_mul_of_nonneg_left
                (Work.Analysis.SqAddSq.integral_s_div_sq_add_sq_le hA hs hεpos.le) (by positivity)
          _ = 2 * Real.pi * η / Real.sqrt A := hmodel_bound
      have hP1a : ‖(∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
          - (∫ τ in (0 : ℝ)..ε, jwModel c s τ)‖ ≤ 2 * Real.pi * η / Real.sqrt A := by
        rw [← hsub]
        exact le_trans (intervalIntegral.norm_integral_le_integral_norm hεpos.le) hbnd
      calc ‖(∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
              - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖
          = ‖((∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
                - (∫ τ in (0 : ℝ)..ε, jwModel c s τ))
              + ((∫ τ in (0 : ℝ)..ε, jwModel c s τ)
                - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0))‖ := by
              congr 1; ring
        _ ≤ ‖(∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
                - (∫ τ in (0 : ℝ)..ε, jwModel c s τ)‖
              + ‖(∫ τ in (0 : ℝ)..ε, jwModel c s τ)
                - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖ := norm_add_le _ _
        _ ≤ 2 * Real.pi * η / Real.sqrt A + η := add_le_add hP1a hE1s'
    -- the piece `[2π - ε, 2π]`
    have hP3 : ‖(∫ τ in (2 * Real.pi - ε)..(2 * Real.pi), jwIntegrand c s τ)
        - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖
        ≤ 2 * Real.pi * η / Real.sqrt A + η := by
      have hcomp : (∫ τ in (2 * Real.pi - ε)..(2 * Real.pi), jwIntegrand c s τ)
          = ∫ σ in (0 : ℝ)..ε, jwIntegrand c s (2 * Real.pi - σ) := by
        rw [intervalIntegral.integral_comp_sub_left (jwIntegrand c s) (2 * Real.pi), sub_zero]
      have hper : (∫ σ in (0 : ℝ)..ε, jwIntegrand c s (2 * Real.pi - σ))
          = ∫ σ in (0 : ℝ)..ε, jwIntegrand c s (-σ) :=
        intervalIntegral.integral_congr (fun σ _ => jwIntegrand_periodic c σ s)
      rw [hcomp, hper]
      have hpointn : ∀ σ : ℝ, |σ| ≤ ε →
          ‖jwIntegrand c s (-σ) - jwModel c s (-σ)‖ ≤ 4 * η * (s / (A * σ ^ 2 + s ^ 2)) := by
        intro σ hσ
        have hσδ : |(-σ)| ≤ δ₁ := by rw [abs_neg]; exact le_trans hσ hεδ
        have hb := norm_integrand_sub_model_le_of_deriv_ne_zero c hreg hη.le hη8 (hexp (-σ) hσδ) (hder (-σ) hσδ)
          (hne (-σ)) hs
        rw [← hAdef] at hb
        rw [show 4 * η * s / (A * (-σ) ^ 2 + s ^ 2) = 4 * η * (s / (A * σ ^ 2 + s ^ 2))
          from by ring_nf] at hb
        simpa only [jwIntegrand, jwModel] using hb
      have heven : (∫ σ in (0 : ℝ)..ε, jwModel c s (-σ))
          = ∫ σ in (0 : ℝ)..ε, jwModel c s σ :=
        intervalIntegral.integral_congr (fun σ _ => jwModel_even c s σ)
      have hsubn : ∫ σ in (0 : ℝ)..ε, (jwIntegrand c s (-σ) - jwModel c s (-σ))
          = (∫ σ in (0 : ℝ)..ε, jwIntegrand c s (-σ))
            - (∫ σ in (0 : ℝ)..ε, jwModel c s (-σ)) :=
        intervalIntegral.integral_sub ((hcontf.comp continuous_neg).intervalIntegrable _ _)
          ((hcontg.comp continuous_neg).intervalIntegrable _ _)
      have hbndn : ‖(∫ σ in (0 : ℝ)..ε, jwIntegrand c s (-σ))
          - (∫ σ in (0 : ℝ)..ε, jwModel c s σ)‖ ≤ 2 * Real.pi * η / Real.sqrt A := by
        rw [← heven, ← hsubn]
        refine le_trans (intervalIntegral.norm_integral_le_integral_norm hεpos.le) ?_
        calc ∫ σ in (0 : ℝ)..ε, ‖jwIntegrand c s (-σ) - jwModel c s (-σ)‖
            ≤ ∫ σ in (0 : ℝ)..ε, 4 * η * (s / (A * σ ^ 2 + s ^ 2)) := by
              refine intervalIntegral.integral_mono_on hεpos.le ?_ ?_ ?_
              · exact ((hcontf.comp continuous_neg).sub (hcontg.comp continuous_neg)).norm.intervalIntegrable _ _
              · exact hboundfun_cont.intervalIntegrable _ _
              · intro x hx
                exact hpointn x (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          _ = (4 * η) * ∫ σ in (0 : ℝ)..ε, s / (A * σ ^ 2 + s ^ 2) :=
              intervalIntegral.integral_const_mul _ _
          _ ≤ (4 * η) * ((Real.pi / 2) / Real.sqrt A) :=
              mul_le_mul_of_nonneg_left
                (Work.Analysis.SqAddSq.integral_s_div_sq_add_sq_le hA hs hεpos.le) (by positivity)
          _ = 2 * Real.pi * η / Real.sqrt A := hmodel_bound
      calc ‖(∫ σ in (0 : ℝ)..ε, jwIntegrand c s (-σ))
              - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖
          = ‖((∫ σ in (0 : ℝ)..ε, jwIntegrand c s (-σ))
                - (∫ σ in (0 : ℝ)..ε, jwModel c s σ))
              + ((∫ σ in (0 : ℝ)..ε, jwModel c s σ)
                - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0))‖ := by
              congr 1; ring
        _ ≤ ‖(∫ σ in (0 : ℝ)..ε, jwIntegrand c s (-σ))
                - (∫ σ in (0 : ℝ)..ε, jwModel c s σ)‖
              + ‖(∫ σ in (0 : ℝ)..ε, jwModel c s σ)
                - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖ := norm_add_le _ _
        _ ≤ 2 * Real.pi * η / Real.sqrt A + η := add_le_add hbndn hE1s'
    -- the middle piece
    have hP2 : ‖(∫ τ in ε..(2 * Real.pi - ε), jwIntegrand c s τ)‖ ≤ η := by
      have h5 : 0 < mc ^ 2 := by positivity
      have h6 : 0 < mc ^ 2 - s ^ 2 := by nlinarith [hsmc, hmcpos]
      have h4 : 2 * s ^ 2 < mc ^ 2 := by
        have h1 : 0 < mc / 2 - s := by linarith
        have h2 : 0 < mc / 2 + s := by linarith
        nlinarith [mul_pos h1 h2]
      have hpt : ∀ τ ∈ Set.uIoc ε (2 * Real.pi - ε),
          ‖jwIntegrand c s τ‖ ≤ 2 * s * M₁ / mc ^ 2 := by
        intro τ hτ
        rw [Set.uIoc_of_le hε2π] at hτ
        have hτ1 : ε ≤ τ := le_of_lt hτ.1
        have hτ2 : τ ≤ 2 * Real.pi - ε := hτ.2
        have hfar : mc ≤ ‖c.γ τ - c.γ 0‖ := by
          have h := hmc 0 τ ⟨le_refl 0, by positivity⟩
            ⟨by linarith, by linarith [hεpos]⟩
            (by rw [sub_zero, abs_of_nonneg (by linarith)]; exact hτ1)
            (by rw [sub_zero, abs_of_nonneg (by linarith)]; linarith)
          rwa [norm_sub_rev] at h
        have hden_lb : mc ^ 2 - s ^ 2 ≤
            ‖(c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2‖ := by
          have h1 : ‖(c.γ τ - c.γ 0) ^ 2‖ ≤
              ‖(c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2‖
                + ‖(s : ℂ) ^ 2 * (unitTangent c 0) ^ 2‖ := by
            have h2 := norm_add_le ((c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2)
              (-((s : ℂ) ^ 2 * (unitTangent c 0) ^ 2))
            simpa using h2
          have h3 : ‖(s : ℂ) ^ 2 * (unitTangent c 0) ^ 2‖ = s ^ 2 := by
            rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hs, hu]
            ring
          rw [norm_pow, h3] at h1
          have h4' : mc ^ 2 ≤ ‖c.γ τ - c.γ 0‖ ^ 2 := by nlinarith [hmcpos]
          linarith
        have hnum : ‖(s : ℂ) * deriv c.γ τ‖ = s * ‖deriv c.γ τ‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
        have hden_pos : 0 < ‖(c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2‖ :=
          norm_pos_iff.mpr (hne τ)
        have hnum2 : ‖(s : ℂ) * deriv c.γ τ‖ ≤ s * M₁ := by
          rw [hnum]; exact mul_le_mul_of_nonneg_left (hM₁up τ) hs.le
        calc ‖jwIntegrand c s τ‖
            = ‖(s : ℂ) * deriv c.γ τ‖
              / ‖(c.γ τ - c.γ 0) ^ 2 + (s : ℂ) ^ 2 * (unitTangent c 0) ^ 2‖ := by
                rw [jwIntegrand, norm_div]
          _ ≤ s * M₁ / (mc ^ 2 - s ^ 2) := div_le_div₀ (by positivity) hnum2 h6 hden_lb
          _ ≤ 2 * s * M₁ / mc ^ 2 := by
                rw [div_le_div_iff₀ h6 h5]
                have h7 : mc ^ 2 ≤ 2 * (mc ^ 2 - s ^ 2) := by linarith [h4]
                calc s * M₁ * mc ^ 2 ≤ s * M₁ * (2 * (mc ^ 2 - s ^ 2)) :=
                      mul_le_mul_of_nonneg_left h7 (by positivity)
                  _ = 2 * s * M₁ * (mc ^ 2 - s ^ 2) := by ring
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hpt) ?_
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.pi - ε - ε)]
      have h7 : 2 * s * M₁ / mc ^ 2 * (2 * Real.pi - ε - ε) ≤ 4 * Real.pi * s * M₁ / mc ^ 2 := by
        have h8 : 2 * Real.pi - ε - ε ≤ 2 * Real.pi := by linarith [hεpos]
        have h9 : 0 ≤ 2 * s * M₁ / mc ^ 2 := by positivity
        calc 2 * s * M₁ / mc ^ 2 * (2 * Real.pi - ε - ε)
            ≤ 2 * s * M₁ / mc ^ 2 * (2 * Real.pi) := mul_le_mul_of_nonneg_left h8 h9
          _ = 4 * Real.pi * s * M₁ / mc ^ 2 := by ring
      have h10 : 4 * Real.pi * s * M₁ < s * (8 * M₁ * Real.pi + 1) := by
        have hpos : 0 < s * (4 * M₁ * Real.pi + 1) := by positivity
        have hdiff : s * (8 * M₁ * Real.pi + 1) - 4 * Real.pi * s * M₁
            = s * (4 * M₁ * Real.pi + 1) := by ring
        linarith only [hpos, hdiff]
      have h11 : 4 * Real.pi * s * M₁ < η * mc ^ 2 := lt_trans h10 hsη
      have h12 : 4 * Real.pi * s * M₁ / mc ^ 2 < η := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < mc ^ 2)]
        exact h11
      exact le_trans h7 h12.le
    -- the split of the integral
    have htot : (∫ τ in (0 : ℝ)..(2 * Real.pi), jwIntegrand c s τ)
        = (∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
          + (∫ τ in ε..(2 * Real.pi - ε), jwIntegrand c s τ)
          + (∫ τ in (2 * Real.pi - ε)..(2 * Real.pi), jwIntegrand c s τ) := by
      have hs1 := intervalIntegral.integral_add_adjacent_intervals
        (hcontf.intervalIntegrable (μ := MeasureTheory.volume) 0 ε)
        (hcontf.intervalIntegrable (μ := MeasureTheory.volume) ε (2 * Real.pi - ε))
      have hs2 := intervalIntegral.integral_add_adjacent_intervals
        ((hcontf.intervalIntegrable (μ := MeasureTheory.volume) 0 ε).trans
          (hcontf.intervalIntegrable (μ := MeasureTheory.volume) ε (2 * Real.pi - ε)))
        (hcontf.intervalIntegrable (μ := MeasureTheory.volume) (2 * Real.pi - ε) (2 * Real.pi))
      rw [← hs2, ← hs1]
    have hfinal : ‖(∫ τ in (0 : ℝ)..(2 * Real.pi), jwIntegrand c s τ)
        - (Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖
        ≤ (2 * Real.pi * η / Real.sqrt A + η) + η + (2 * Real.pi * η / Real.sqrt A + η) := by
      have hsplit : (∫ τ in (0 : ℝ)..(2 * Real.pi), jwIntegrand c s τ)
          - (Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0)
          = ((∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
              - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0))
            + (∫ τ in ε..(2 * Real.pi - ε), jwIntegrand c s τ)
            + ((∫ τ in (2 * Real.pi - ε)..(2 * Real.pi), jwIntegrand c s τ)
              - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0)) := by
        rw [htot]; ring
      rw [hsplit]
      have h1 : ‖((∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
              - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0))
            + (∫ τ in ε..(2 * Real.pi - ε), jwIntegrand c s τ)
            + ((∫ τ in (2 * Real.pi - ε)..(2 * Real.pi), jwIntegrand c s τ)
              - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0))‖
          ≤ ‖((∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
              - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0))
            + (∫ τ in ε..(2 * Real.pi - ε), jwIntegrand c s τ)‖
            + ‖((∫ τ in (2 * Real.pi - ε)..(2 * Real.pi), jwIntegrand c s τ)
              - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0))‖ := norm_add_le _ _
      have h2 : ‖((∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
              - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0))
            + (∫ τ in ε..(2 * Real.pi - ε), jwIntegrand c s τ)‖
          ≤ ‖(∫ τ in (0 : ℝ)..ε, jwIntegrand c s τ)
              - (Real.pi / 2 : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖
            + ‖(∫ τ in ε..(2 * Real.pi - ε), jwIntegrand c s τ)‖ := norm_add_le _ _
      linarith only [h1, h2, hP1, hP2, hP3]
    calc ‖(∫ τ in (0 : ℝ)..(2 * Real.pi), jwIntegrand c s τ)
            - (Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖
        ≤ (2 * Real.pi * η / Real.sqrt A + η) + η + (2 * Real.pi * η / Real.sqrt A + η) := hfinal
      _ ≤ C * η := by
          rw [hCdef]
          have e1 : (4 * Real.pi / Real.sqrt A + 3) * η
              = 4 * Real.pi * η / Real.sqrt A + 3 * η := by ring
          rw [e1]
          have e2 : 4 * Real.pi * η / Real.sqrt A = 2 * (2 * Real.pi * η / Real.sqrt A) := by ring
          rw [e2]
          linarith only
  -- choose the smallness parameter and conclude
  set η₀ : ℝ := min (min 1 (‖deriv c.γ 0‖ / 8)) (δ' / (C + 1)) with hη₀def
  have hη₀pos : 0 < η₀ := by
    rw [hη₀def]
    exact lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hη₀1 : η₀ ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hη₀8 : η₀ ≤ ‖deriv c.γ 0‖ / 8 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hη₀C : C * η₀ < δ' := by
    have hle : η₀ ≤ δ' / (C + 1) := min_le_right _ _
    have h1 : C * η₀ ≤ C * (δ' / (C + 1)) := mul_le_mul_of_nonneg_left hle hCpos.le
    have h2 : C * (δ' / (C + 1)) < δ' := by
      rw [show C * (δ' / (C + 1)) = C * δ' / (C + 1) from by rw [mul_div_assoc']]
      rw [div_lt_iff₀ (by linarith [hCpos])]
      nlinarith [hδ', hCpos]
    linarith
  filter_upwards [key η₀ hη₀pos hη₀8 hη₀1] with s hs
  rw [dist_eq_norm]
  have hfin : ‖(∫ τ in (0 : ℝ)..(2 * Real.pi), jwIntegrand c s τ)
      - (Real.pi : ℂ) * (starRingEnd ℂ) (unitTangent c 0)‖ < δ' :=
    lt_of_le_of_lt hs hη₀C
  simpa only [jwIntegrand] using hfin

end

end Work.Smooth.JordanSeparation
