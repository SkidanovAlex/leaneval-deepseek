import Mathlib
import Submission.Commons.Analysis.Maximal.real_maximal_strong_type
import Submission.Commons.Analysis.HardyLittlewood.lintegral_convolution_radial_decreasing_measurable_le_hlMax
import Submission.Commons.Analysis.Fourier.one_sided_geometric_maximal_l2

open MeasureTheory
open scoped ENNReal

open Commons.Analysis.Maximal (hlMax)

namespace Commons.Analysis.Fourier

/-! ### Elementary `enorm` facts for `ℂ` -/

lemma enorm_norm_eq_enorm (z : ℂ) : ‖(‖z‖ : ℝ)‖ₑ = ‖z‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg z), enorm_eq_nnnorm,
    ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

/-! ### A radially decreasing majorant for a Schwartz function -/

/-- Every Schwartz function on `ℝ` has an even, radially non-increasing `ℝ≥0∞`-valued
majorant with finite, positive integral. -/
lemma exists_radial_decreasing_majorant (Ψ : SchwartzMap ℝ ℂ) :
    ∃ K : ℝ → ℝ≥0∞, (∀ z : ℝ, K (-z) = K z) ∧
      (∀ x y : ℝ, 0 ≤ x → x ≤ y → K y ≤ K x) ∧ Measurable K ∧
      (∀ z : ℝ, ‖Ψ z‖ₑ ≤ K z) ∧ (∫⁻ z, K z) ≠ ⊤ ∧ 0 < ∫⁻ z, K z := by
  obtain ⟨C0, hC0pos, hC0⟩ := Ψ.decay 0 0
  obtain ⟨C4, hC4pos, hC4⟩ := Ψ.decay 4 0
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at hC0 hC4
  set A : ℝ := 16 * max 1 (C0 + C4) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hAle : 16 * (C0 + C4) ≤ A := by
    rw [hAdef]
    have : C0 + C4 ≤ max 1 (C0 + C4) := le_max_right _ _
    linarith
  have hmeas : Measurable (fun z : ℝ => ENNReal.ofReal (A * (1 + ‖z‖) ^ (-4:ℝ))) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.mul ((continuous_const.add continuous_norm).rpow_const
        (fun z => Or.inl (ne_of_gt (by positivity : (0:ℝ) < 1 + ‖z‖)))).measurable))
  refine ⟨fun z => ENNReal.ofReal (A * (1 + ‖z‖) ^ (-4:ℝ)), ?_, ?_, hmeas, ?_, ?_, ?_⟩
  · intro z
    simp only [norm_neg]
  · intro x y hx hxy
    have h1 : (1 + ‖x‖) ≤ (1 + ‖y‖) := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)]
      linarith
    have h2 : (1 + ‖y‖) ^ (-4:ℝ) ≤ (1 + ‖x‖) ^ (-4:ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h2 hApos.le)
  · intro z
    have ht : 0 ≤ ‖z‖ := norm_nonneg z
    have hpow : (1 + ‖z‖) ^ (4:ℕ) ≤ 16 * (1 + ‖z‖ ^ 4) := by
      have hmax4 : (max 1 ‖z‖) ^ 4 ≤ 1 + ‖z‖ ^ 4 := by
        rcases max_cases (1:ℝ) ‖z‖ with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; norm_num
        · rw [h]; nlinarith [pow_nonneg ht 4]
      have h1 : 1 + ‖z‖ ≤ 2 * max 1 ‖z‖ := by
        have a := le_max_left (1:ℝ) ‖z‖
        have b := le_max_right (1:ℝ) ‖z‖
        linarith
      calc (1 + ‖z‖) ^ (4:ℕ) ≤ (2 * max 1 ‖z‖) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
        _ = 16 * (max 1 ‖z‖) ^ 4 := by rw [mul_pow]; norm_num
        _ ≤ 16 * (1 + ‖z‖ ^ 4) := by nlinarith
    have hbound : ‖Ψ z‖ * (1 + ‖z‖) ^ (4:ℕ) ≤ A := by
      have h1 := mul_le_mul_of_nonneg_left hpow (norm_nonneg (Ψ z))
      have h2 : ‖Ψ z‖ * (16 * (1 + ‖z‖ ^ 4)) = 16 * (‖Ψ z‖ + ‖z‖ ^ 4 * ‖Ψ z‖) := by ring
      have h3 : 16 * (‖Ψ z‖ + ‖z‖ ^ 4 * ‖Ψ z‖) ≤ 16 * (C0 + C4) := by
        have := hC0 z
        have := hC4 z
        linarith
      linarith
    have hbound' : ‖Ψ z‖ * (1 + ‖z‖) ^ (4:ℝ) ≤ A := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      exact hbound
    have h : ‖Ψ z‖ ≤ A * (1 + ‖z‖) ^ (-4:ℝ) := by
      rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + ‖z‖) (4:ℝ), ← div_eq_mul_inv]
      exact (le_div_iff₀ (by positivity : (0:ℝ) < (1 + ‖z‖) ^ (4:ℝ))).mpr hbound'
    rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal h
  · have hint : Integrable (fun z : ℝ => A * (1 + ‖z‖) ^ (-4:ℝ)) volume := by
      have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 4) (by
        simp [Module.finrank_self])
      exact h.const_mul A
    exact (lintegral_ofReal_ne_top_iff_integrable hint.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z =>
        mul_nonneg hApos.le (Real.rpow_nonneg (by positivity) _))).mpr hint
  · rw [lintegral_pos_iff_support hmeas]
    have hsupp : Function.support (fun z : ℝ => ENNReal.ofReal (A * (1 + ‖z‖) ^ (-4:ℝ)))
        = Set.univ := by
      ext z
      simp only [Function.mem_support, Set.mem_univ, iff_true, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos hApos (Real.rpow_pos_of_pos (by positivity) _)
    rw [hsupp, Real.volume_univ]
    exact ENNReal.zero_lt_top

/-! ### Dilated radially decreasing kernels -/

/-- Convolution with a dilated, `L¹`-normalised radially non-increasing kernel is dominated by
`(∫⁻ K) · hlMax g`, uniformly in the dilation parameter. -/
theorem lintegral_convolution_dilate_ae_le_hlMax (K : ℝ → ℝ≥0∞) (hsym : ∀ y : ℝ, K (-y) = K y)
    (hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → K y ≤ K x)
    (g : ℝ → ℝ≥0∞) (hg : AEMeasurable g volume) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫⁻ y, g y * (ENNReal.ofReal t⁻¹ * K ((x - y) / t))
      ≤ (∫⁻ z, K z) * hlMax g x := by
  have hKmeas : Measurable K :=
    Commons.Analysis.HardyLittlewood.measurable_of_even_antitone_on_nonneg hsym hmono
  set Kt : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal t⁻¹ * K (z / t) with hKtdef
  have hsymt : ∀ y : ℝ, Kt (-y) = Kt y := by
    intro y
    simp only [hKtdef]
    rw [show -y / t = -(y / t) by ring, hsym (y / t)]
  have hmonot : ∀ x y : ℝ, 0 ≤ x → x ≤ y → Kt y ≤ Kt x := by
    intro x y hx hxy
    have h1 : 0 ≤ x / t := div_nonneg hx ht.le
    have h2 : x / t ≤ y / t := by gcongr
    have h3 := hmono (x / t) (y / t) h1 h2
    simp only [hKtdef]
    exact mul_le_mul_of_nonneg_left h3 (show (0:ℝ≥0∞) ≤ ENNReal.ofReal t⁻¹ from bot_le)
  have hKtint : ∫⁻ z, Kt z = ∫⁻ z, K z := by
    have hsub : ∫⁻ z, K (z / t) = ENNReal.ofReal t * ∫⁻ z, K z := by
      have hmap : Measure.map (fun w : ℝ => t * w) volume = ENNReal.ofReal t⁻¹ • volume := by
        rw [Real.map_volume_mul_left ht.ne', abs_of_pos (inv_pos.mpr ht)]
      have hL : ∫⁻ z, K (z / t) ∂(Measure.map (fun w : ℝ => t * w) volume) = ∫⁻ w, K w := by
        rw [lintegral_map (f := fun z : ℝ => K (z / t)) (g := fun w : ℝ => t * w)
          (hKmeas.comp (measurable_id.div_const t)) (measurable_const.mul measurable_id)]
        exact lintegral_congr fun w => by rw [mul_div_cancel_left₀ _ ht.ne']
      have hR : ∫⁻ z, K (z / t) ∂(ENNReal.ofReal t⁻¹ • volume)
          = ENNReal.ofReal t⁻¹ * ∫⁻ z, K (z / t) := lintegral_smul_measure _ _
      have h2 : ∫⁻ w, K w = ENNReal.ofReal t⁻¹ * ∫⁻ z, K (z / t) := by
        rw [← hL, hmap, hR]
      rw [h2, ENNReal.ofReal_inv_of_pos ht, ← mul_assoc,
        ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top, one_mul]
    simp only [hKtdef]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hsub, ENNReal.ofReal_inv_of_pos ht,
      ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top,
      one_mul]
  have hae : g =ᵐ[volume] hg.mk g := hg.ae_eq_mk
  have hconv : ∫⁻ y, g y * Kt (x - y) = ∫⁻ y, hg.mk g y * Kt (x - y) :=
    lintegral_congr_ae (hae.mul (Filter.EventuallyEq.refl _ _))
  have hM : hlMax (hg.mk g) x = hlMax g x := (OneSided.hlMax_congr_ae hae x).symm
  calc ∫⁻ y, g y * (ENNReal.ofReal t⁻¹ * K ((x - y) / t))
      = ∫⁻ y, g y * Kt (x - y) := by simp only [hKtdef]
    _ = ∫⁻ y, hg.mk g y * Kt (x - y) := hconv
    _ ≤ (∫⁻ z, Kt z) * hlMax (hg.mk g) x :=
        Commons.Analysis.HardyLittlewood.lintegral_convolution_radial_decreasing_measurable_le_hlMax
          Kt hsymt hmonot (hg.mk g) hg.measurable_mk x
    _ = (∫⁻ z, K z) * hlMax g x := by rw [hKtint, hM]

/-- **Maximal dilation of a convolution with a Schwartz window is `L²`-bounded.**  For a Schwartz
function `Ψ` and `g ∈ L²(ℝ)`, the maximal function over all scales `t > 0` of the convolution of
`g` with the `L¹`-normalised dilates `t⁻¹Ψ(·/t)` of `Ψ` is bounded on `L²(ℝ)`. -/
theorem maximal_dilation_convolution_l2 (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ → ℂ), MemLp g 2 (volume : Measure ℝ) →
      ∫⁻ x, (⨆ t : {t : ℝ // 0 < t},
          ‖∫ y : ℝ, g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ) ^ (2 : ℝ)
        ≤ ENNReal.ofReal C * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) := by
  obtain ⟨K, hsym, hmono, hKmeas, hKmaj, hKtop, hKpos⟩ := exists_radial_decreasing_majorant Ψ
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Maximal.real_maximal_strong_type 2 (by norm_num)
  set d : ℝ := (∫⁻ z, K z).toReal with hddef
  have hdpos : 0 < d := ENNReal.toReal_pos hKpos.ne' hKtop
  have hKeq : ∫⁻ z, K z = ENNReal.ofReal d := (ENNReal.ofReal_toReal hKtop).symm
  refine ⟨d ^ 2 * C₀ ^ 2, by positivity, fun g hg => ?_⟩
  have hgenorm : AEMeasurable (fun y : ℝ => ‖g y‖ₑ) volume :=
    hg.aestronglyMeasurable.aemeasurable.enorm
  have hpt : ∀ x : ℝ, (⨆ t : {t : ℝ // 0 < t},
        ‖∫ y : ℝ, g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ)
      ≤ (∫⁻ z, K z) * hlMax (fun y : ℝ => ‖g y‖ₑ) x := by
    intro x
    refine iSup_le fun t => ?_
    have ht : (0 : ℝ) < (t : ℝ) := t.2
    calc ‖∫ y : ℝ, g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ
        ≤ ∫⁻ y, ‖g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, ‖g y‖ₑ * (ENNReal.ofReal (t : ℝ)⁻¹ * K ((x - y) / (t : ℝ))) := by
          refine lintegral_mono fun y => ?_
          have h2 : ‖(t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ)))‖ₑ
              ≤ ENNReal.ofReal (t : ℝ)⁻¹ * K ((x - y) / (t : ℝ)) := by
            refine le_trans (enorm_smul_le (r := (t : ℝ)⁻¹)
              (x := Ψ ((x - y) / (t : ℝ)))) ?_
            rw [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr ht)]
            exact mul_le_mul_of_nonneg_left (hKmaj _) bot_le
          rw [enorm_mul]
          exact mul_le_mul_of_nonneg_left h2 bot_le
      _ ≤ (∫⁻ z, K z) * hlMax (fun y : ℝ => ‖g y‖ₑ) x :=
          lintegral_convolution_dilate_ae_le_hlMax K hsym hmono _ hgenorm ht x
  calc ∫⁻ x, (⨆ t : {t : ℝ // 0 < t},
        ‖∫ y : ℝ, g y * ((t : ℝ)⁻¹ • (Ψ ((x - y) / (t : ℝ))))‖ₑ) ^ (2 : ℝ)
      ≤ ∫⁻ x, ((∫⁻ z, K z) * hlMax (fun y : ℝ => ‖g y‖ₑ) x) ^ (2 : ℝ) :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) (by norm_num)
    _ = (∫⁻ z, K z) ^ 2 * ∫⁻ x, (hlMax (fun y : ℝ => ‖g y‖ₑ) x) ^ 2 := by
        have h1 : ∀ x : ℝ, ((∫⁻ z, K z) * hlMax (fun y : ℝ => ‖g y‖ₑ) x) ^ (2 : ℝ)
            = (∫⁻ z, K z) ^ 2 * (hlMax (fun y : ℝ => ‖g y‖ₑ) x) ^ 2 := by
          intro x
          rw [ENNReal.rpow_two, mul_pow]
        simp only [h1]
        exact lintegral_const_mul' ((∫⁻ z, K z) ^ 2)
          (fun x => (hlMax (fun y : ℝ => ‖g y‖ₑ) x) ^ 2) (ENNReal.pow_ne_top hKtop)
    _ ≤ (∫⁻ z, K z) ^ 2 * (ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        simpa only [enorm_norm_eq_enorm, hlMax, ENNReal.rpow_two, Real.rpow_two]
          using hC₀ (fun y : ℝ => ‖g y‖)
    _ = ENNReal.ofReal (d ^ 2 * C₀ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) := by
        have h1 : (∫⁻ z, K z) ^ 2 * (ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ 2)
            = ENNReal.ofReal (d ^ 2 * C₀ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
          rw [hKeq, ← ENNReal.ofReal_pow hdpos.le, ENNReal.ofReal_mul (by positivity),
            mul_assoc]
        rw [h1]
        simp only [ENNReal.rpow_two]


end Commons.Analysis.Fourier
