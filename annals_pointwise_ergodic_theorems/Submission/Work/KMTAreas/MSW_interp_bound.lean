import Mathlib
import Submission.Work.KMTAreas.MSW_tsum_norm_bound
import Submission.Work.KMTAreas.MSW_tsum_holder
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal
open MeasureTheory

namespace Work.KMTAreas

/-- The uniform `ℓᵖ(ℤ) → Lᵖ(ℝ)` bound for the "sampling/Shannon interpolation" operator with a
Schwartz kernel: `‖∑_{m∈s} u_m K(·+m)‖_{Lᵖ(ℝ)} ≤ C ‖u‖_{ℓᵖ(ℤ)}` with a single constant `C` for
all `1 ≤ p ≤ ∞`. -/
theorem MSW_interp_bound (K : SchwartzMap ℝ ℂ) :
    ∃ C : NNReal, 0 < C ∧ ∀ (p : ENNReal), 1 ≤ p → ∀ (s : Finset ℤ) (u : ℤ → ℂ),
      (∀ m, m ∉ s → u m = 0) →
      MeasureTheory.eLpNorm (fun y : ℝ => Finset.sum s (fun m => u m * K (y + m))) p
          MeasureTheory.volume
        ≤ ENNReal.ofReal (C : ℝ) * MeasureTheory.eLpNorm u p MeasureTheory.Measure.count := by
  classical
  obtain ⟨A, hA⟩ := MSW_tsum_norm_bound K
  have hKint : Integrable (K : ℝ → ℂ) := K.integrable (μ := volume)
  set B : ENNReal := ∫⁻ y : ℝ, ‖K y‖ₑ ∂volume with hB
  have hBtop : B ≠ ⊤ := by
    rw [hB, ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hKint]
    exact ENNReal.ofReal_ne_top
  have hAtop : (A : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  set C₀ : ENNReal := (A : ENNReal) + B + 1 with hC₀
  have hAC₀ : (A : ENNReal) ≤ C₀ := by rw [hC₀]; exact le_self_add.trans le_self_add
  have hBC₀ : B ≤ C₀ := by rw [hC₀]; exact le_add_self.trans le_self_add
  have hvol : (volume : Measure ℝ) ≠ 0 := fun hcon => by
    have := congrArg (fun μ : Measure ℝ => μ Set.univ) hcon
    simp at this
  have hcoe : ENNReal.ofReal (((A + B.toNNReal + 1 : NNReal)) : ℝ) = C₀ := by
    rw [ENNReal.ofReal_coe_nnreal, hC₀]
    push_cast
    rw [ENNReal.coe_toNNReal hBtop]
  refine ⟨A + B.toNNReal + 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one le_add_self
  · rw [hcoe]
    intro p hp1 s u hu
    set f : ℝ → ℂ := fun y => ∑ m ∈ s, u m * K (y + m) with hf
    have hu_fin : ∀ m : ℤ, ‖u m‖ₑ ≠ ⊤ := fun m => by simp
    have hpt (y : ℝ) : ‖f y‖ₑ ≤ ∑' m : ℤ, ‖u m‖ₑ * ‖K (y + m)‖ₑ := by
      show ‖∑ m ∈ s, u m * K (y + m)‖ₑ ≤ _
      refine (enorm_sum_le s (fun m => u m * K (y + m))).trans ?_
      refine (Finset.sum_le_sum fun m _ => ?_).trans (ENNReal.sum_le_tsum s)
      rw [enorm_mul]
    have hAEM1 : ∀ m : ℤ,
        AEMeasurable (fun y : ℝ => ‖u m‖ₑ * ‖K (y + m)‖ₑ) volume := by
      intro m
      exact (measurable_const.mul (continuous_enorm.measurable.comp
        (K.continuous.measurable.comp (measurable_id.add measurable_const)))).aemeasurable
    have hAEMR : ∀ (r : ℝ) (m : ℤ),
        AEMeasurable (fun y : ℝ => ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ) volume := by
      intro r m
      exact (measurable_const.mul (continuous_enorm.measurable.comp
        (K.continuous.measurable.comp (measurable_id.add measurable_const)))).aemeasurable
    by_cases hp : p = ⊤
    · -- ===== p = ⊤ =====
      rw [hp]
      have hsup : (⨆ m : ℤ, ‖u m‖ₑ) ≤ eLpNorm u ⊤ (Measure.count : Measure ℤ) := by
        refine iSup_le fun m => ?_
        rw [MeasureTheory.eLpNorm_exponent_top (hf := by pw_aesm), MeasureTheory.eLpNormEssSup_eq_essSup_enorm]
        have h := ENNReal.ae_le_essSup (μ := (Measure.count : Measure ℤ)) (fun m : ℤ => ‖u m‖ₑ)
        rw [MeasureTheory.Measure.ae_count_iff] at h
        exact h m
      have hpttop (y : ℝ) : ‖f y‖ₑ ≤ (A : ENNReal) * (⨆ m : ℤ, ‖u m‖ₑ) := by
        calc ‖f y‖ₑ ≤ ∑' m : ℤ, ‖u m‖ₑ * ‖K (y + m)‖ₑ := hpt y
          _ = ∑ m ∈ s, ‖u m‖ₑ * ‖K (y + m)‖ₑ := by
              rw [tsum_eq_sum (s := s)]
              intro m hm
              rw [hu m hm, enorm_zero, zero_mul]
          _ ≤ (⨆ m : ℤ, ‖u m‖ₑ) * ∑ m ∈ s, ‖K (y + m)‖ₑ := by
              rw [Finset.mul_sum]
              exact Finset.sum_le_sum fun m _ =>
                mul_le_mul' (le_iSup (fun m : ℤ => ‖u m‖ₑ) m) le_rfl
          _ ≤ (⨆ m : ℤ, ‖u m‖ₑ) * (A : ENNReal) :=
              mul_le_mul' le_rfl ((ENNReal.sum_le_tsum s).trans (hA y))
          _ = (A : ENNReal) * (⨆ m : ℤ, ‖u m‖ₑ) := mul_comm _ _
      have h2top : eLpNorm f ⊤ volume ≤ (A : ENNReal) * (⨆ m : ℤ, ‖u m‖ₑ) := by
        rw [MeasureTheory.eLpNorm_exponent_top (hf := by pw_aesm), MeasureTheory.eLpNormEssSup_eq_essSup_enorm]
        calc essSup (fun y : ℝ => ‖f y‖ₑ) volume
            ≤ essSup (fun _ : ℝ => (A : ENNReal) * (⨆ m : ℤ, ‖u m‖ₑ)) volume :=
              essSup_mono_ae (Filter.Eventually.of_forall hpttop)
          _ = (A : ENNReal) * (⨆ m : ℤ, ‖u m‖ₑ) := essSup_const _ hvol
      calc eLpNorm f ⊤ volume ≤ (A : ENNReal) * (⨆ m : ℤ, ‖u m‖ₑ) := h2top
        _ ≤ C₀ * eLpNorm u ⊤ (Measure.count : Measure ℤ) := mul_le_mul' hAC₀ hsup
    · -- ===== p < ⊤ =====
      have hp0 : p ≠ 0 := by
        intro h0
        rw [h0] at hp1
        exact absurd hp1 (not_le_of_gt (by norm_num : (0 : ENNReal) < 1))
      set r : ℝ := p.toReal with hr_def
      have hr_ge : 1 ≤ r := by
        rw [hr_def]
        simpa using ENNReal.toReal_mono hp hp1
      have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr_ge
      have hrne : r ≠ 0 := by linarith
      have hr1m : (0 : ℝ) ≤ 1 - 1 / r := by
        have h1 : 1 / r ≤ 1 := by rw [div_le_one (by linarith : (0 : ℝ) < r)]; exact hr_ge
        linarith
      have hp_eq : p = ENNReal.ofReal r := by rw [hr_def, ENNReal.ofReal_toReal hp]
      rw [hp_eq]
      rcases lt_or_eq_of_le hr_ge with hr_gt | hr_eq
      · -- ===== 1 < r =====
        have key (y : ℝ) : ‖f y‖ₑ ^ r ≤
            (A : ENNReal) ^ (r - 1) * ∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ := by
          have h2 : ∑' m : ℤ, ‖u m‖ₑ * ‖K (y + m)‖ₑ
              ≤ (∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ) ^ (1 / r)
                * (A : ENNReal) ^ (1 - 1 / r) := by
            refine (MSW_tsum_holder r hr_gt (fun m : ℤ => ‖u m‖ₑ)
              (fun m : ℤ => ‖K (y + m)‖ₑ)).trans ?_
            exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hA y) hr1m)
          calc ‖f y‖ₑ ^ r ≤ (∑' m : ℤ, ‖u m‖ₑ * ‖K (y + m)‖ₑ) ^ r :=
                ENNReal.rpow_le_rpow (hpt y) (by positivity)
            _ ≤ ((∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ) ^ (1 / r)
                  * (A : ENNReal) ^ (1 - 1 / r)) ^ r :=
                ENNReal.rpow_le_rpow h2 (by positivity)
            _ = ((∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ) ^ (1 / r)) ^ r
                  * ((A : ENNReal) ^ (1 - 1 / r)) ^ r := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
            _ = (∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ) ^ (1 / r * r)
                  * ((A : ENNReal) ^ (1 - 1 / r)) ^ r := by
                rw [← ENNReal.rpow_mul]
            _ = (∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ) ^ (1 / r * r)
                  * (A : ENNReal) ^ ((1 - 1 / r) * r) := by
                rw [← ENNReal.rpow_mul]
            _ = (∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ) * (A : ENNReal) ^ (r - 1) := by
                rw [show (1 / r) * r = (1 : ℝ) by rw [div_mul_cancel₀ 1 hrne],
                  ENNReal.rpow_one,
                  show (1 - 1 / r) * r = r - 1 by rw [sub_mul, one_mul, div_mul_cancel₀ 1 hrne]]
            _ = (A : ENNReal) ^ (r - 1) * ∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ := mul_comm _ _
        have hint : ∫⁻ y : ℝ, ‖f y‖ₑ ^ r ∂volume
            ≤ (A : ENNReal) ^ (r - 1) * (B * ∫⁻ m : ℤ, ‖u m‖ₑ ^ r ∂Measure.count) := by
          calc ∫⁻ y : ℝ, ‖f y‖ₑ ^ r ∂volume
              ≤ ∫⁻ y : ℝ, (A : ENNReal) ^ (r - 1)
                  * ∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ ∂volume := lintegral_mono key
            _ = (A : ENNReal) ^ (r - 1)
                  * ∫⁻ y : ℝ, ∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ ∂volume := by
                rw [MeasureTheory.lintegral_const_mul' ((A : ENNReal) ^ (r - 1))
                  (fun y : ℝ => ∑' m : ℤ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ)
                  (ENNReal.rpow_ne_top_of_nonneg (by positivity) hAtop)]
            _ = (A : ENNReal) ^ (r - 1)
                  * ∑' m : ℤ, ∫⁻ y : ℝ, ‖u m‖ₑ ^ r * ‖K (y + m)‖ₑ ∂volume := by
                rw [lintegral_tsum (fun m => hAEMR r m)]
            _ = (A : ENNReal) ^ (r - 1)
                  * ∑' m : ℤ, ‖u m‖ₑ ^ r * B := by
                congr 1
                refine tsum_congr fun m => ?_
                rw [MeasureTheory.lintegral_const_mul' (‖u m‖ₑ ^ r) (fun y : ℝ => ‖K (y + m)‖ₑ)
                  (ENNReal.rpow_ne_top_of_nonneg (by positivity) (hu_fin m))]
                congr 1
                rw [MeasureTheory.lintegral_add_right_eq_self (fun x : ℝ => ‖K x‖ₑ)
                  ((m : ℤ) : ℝ), ← hB]
            _ = (A : ENNReal) ^ (r - 1) * (B * ∫⁻ m : ℤ, ‖u m‖ₑ ^ r ∂Measure.count) := by
                congr 1
                calc ∑' m : ℤ, ‖u m‖ₑ ^ r * B = (∑' m : ℤ, ‖u m‖ₑ ^ r) * B :=
                      ENNReal.tsum_mul_right
                  _ = B * (∑' m : ℤ, ‖u m‖ₑ ^ r) := mul_comm _ _
                  _ = B * ∫⁻ m : ℤ, ‖u m‖ₑ ^ r ∂Measure.count := by
                      rw [MeasureTheory.lintegral_count]
        have hAB : (A : ENNReal) ^ ((r - 1) / r) * B ^ (1 / r) ≤ C₀ := by
          calc (A : ENNReal) ^ ((r - 1) / r) * B ^ (1 / r)
              ≤ C₀ ^ ((r - 1) / r) * C₀ ^ (1 / r) :=
                mul_le_mul' (ENNReal.rpow_le_rpow hAC₀ (by positivity))
                  (ENNReal.rpow_le_rpow hBC₀ (by positivity))
            _ = C₀ ^ ((r - 1) / r + 1 / r) :=
                (ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)).symm
            _ = C₀ := by rw [show (r - 1) / r + 1 / r = (1 : ℝ) by
                  rw [← add_div, sub_add_cancel, div_self hrne],
                ENNReal.rpow_one]
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
              (by rw [← hp_eq]; exact hp0) ENNReal.ofReal_ne_top,
            MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
              (by rw [← hp_eq]; exact hp0) ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hr0]
        calc (∫⁻ y : ℝ, ‖f y‖ₑ ^ r ∂volume) ^ (1 / r)
            ≤ ((A : ENNReal) ^ (r - 1) * (B * ∫⁻ m : ℤ, ‖u m‖ₑ ^ r ∂Measure.count)) ^ (1 / r) :=
              ENNReal.rpow_le_rpow hint (by positivity)
          _ = ((A : ENNReal) ^ (r - 1)) ^ (1 / r)
                * ((B * (∫⁻ m : ℤ, ‖u m‖ₑ ^ r ∂Measure.count)) ^ (1 / r)) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          _ = (A : ENNReal) ^ ((r - 1) * (1 / r))
                * (B ^ (1 / r) * (∫⁻ m : ℤ, ‖u m‖ₑ ^ r ∂Measure.count) ^ (1 / r)) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
          _ = (A : ENNReal) ^ ((r - 1) / r)
                * (B ^ (1 / r) * (∫⁻ m : ℤ, ‖u m‖ₑ ^ r ∂Measure.count) ^ (1 / r)) := by
              rw [show (r - 1) * (1 / r) = (r - 1) / r by ring]
          _ = (A : ENNReal) ^ ((r - 1) / r) * B ^ (1 / r)
                * (∫⁻ m : ℤ, ‖u m‖ₑ ^ r ∂Measure.count) ^ (1 / r) := by rw [mul_assoc]
          _ ≤ C₀ * (∫⁻ m : ℤ, ‖u m‖ₑ ^ r ∂Measure.count) ^ (1 / r) := mul_le_mul' hAB le_rfl
      · -- ===== r = 1 =====
        rw [← hr_eq, ENNReal.ofReal_one,
          MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm),
          MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
        have hInt : ∫⁻ y : ℝ, ‖f y‖ₑ ∂volume ≤ B * ∫⁻ m : ℤ, ‖u m‖ₑ ∂Measure.count := by
          calc ∫⁻ y : ℝ, ‖f y‖ₑ ∂volume
              ≤ ∫⁻ y : ℝ, ∑' m : ℤ, ‖u m‖ₑ * ‖K (y + m)‖ₑ ∂volume := lintegral_mono hpt
            _ = ∑' m : ℤ, ∫⁻ y : ℝ, ‖u m‖ₑ * ‖K (y + m)‖ₑ ∂volume :=
                lintegral_tsum hAEM1
            _ = ∑' m : ℤ, ‖u m‖ₑ * B := by
                refine tsum_congr fun m => ?_
                rw [MeasureTheory.lintegral_const_mul' (‖u m‖ₑ) (fun y : ℝ => ‖K (y + m)‖ₑ)
                  (hu_fin m)]
                congr 1
                rw [MeasureTheory.lintegral_add_right_eq_self (fun x : ℝ => ‖K x‖ₑ)
                  ((m : ℤ) : ℝ), ← hB]
            _ = (∑' m : ℤ, ‖u m‖ₑ) * B := ENNReal.tsum_mul_right
            _ = B * (∑' m : ℤ, ‖u m‖ₑ) := mul_comm _ _
            _ = B * ∫⁻ m : ℤ, ‖u m‖ₑ ∂Measure.count := by
                rw [MeasureTheory.lintegral_count]
        calc ∫⁻ y : ℝ, ‖f y‖ₑ ∂volume ≤ B * ∫⁻ m : ℤ, ‖u m‖ₑ ∂Measure.count := hInt
          _ ≤ C₀ * ∫⁻ m : ℤ, ‖u m‖ₑ ∂Measure.count := mul_le_mul' hBC₀ le_rfl

end Work.KMTAreas
