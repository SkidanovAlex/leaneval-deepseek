import Mathlib.MeasureTheory.Integral.Prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Measure.Integral

open MeasureTheory

theorem integral_integral_swap_of_lintegral_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    {w : α → ℝ} {K : α → β → ℝ} {F : β → ℝ}
    (hw0 : ∀ a, 0 ≤ w a) (hK0 : ∀ a b, 0 ≤ K a b) (hF0 : ∀ b, 0 ≤ F b)
    (hwm : AEMeasurable w μ)
    (hKm : AEMeasurable (Function.uncurry K) (μ.prod ν))
    (hFm : AEMeasurable F ν) {C M : ℝ}
    (hC : ∀ a, ∫⁻ b, ENNReal.ofReal (K a b) ∂ν ≤ ENNReal.ofReal C)
    (hM : ∀ b, F b ≤ M) (hw : MeasureTheory.Integrable w μ) :
    MeasureTheory.Integrable (fun p : α × β => w p.1 * K p.1 p.2 * F p.2) (μ.prod ν) ∧
      (∫ p : α × β, w p.1 * K p.1 p.2 * F p.2 ∂(μ.prod ν))
        = ∫ b, F b * (∫ a, w a * K a b ∂μ) ∂ν := by
  have hfa : AEMeasurable (fun p : α × β => w p.1 * K p.1 p.2 * F p.2) (μ.prod ν) := by
    have h1 : AEMeasurable (fun p : α × β => w p.1) (μ.prod ν) := hwm.comp_fst
    have h2 : AEMeasurable (fun p : α × β => K p.1 p.2) (μ.prod ν) := hKm
    have h3 : AEMeasurable (fun p : α × β => F p.2) (μ.prod ν) := hFm.comp_snd
    exact (h1.mul h2).mul h3
  have hGa : AEMeasurable
      (fun p : α × β => ENNReal.ofReal (w p.1) * ENNReal.ofReal (K p.1 p.2) * ENNReal.ofReal (F p.2))
      (μ.prod ν) := by
    have h1 : AEMeasurable (fun p : α × β => ENNReal.ofReal (w p.1)) (μ.prod ν) :=
      hwm.comp_fst.ennreal_ofReal
    have h2 : AEMeasurable (fun p : α × β => ENNReal.ofReal (K p.1 p.2)) (μ.prod ν) :=
      hKm.ennreal_ofReal
    have h3 : AEMeasurable (fun p : α × β => ENNReal.ofReal (F p.2)) (μ.prod ν) :=
      hFm.comp_snd.ennreal_ofReal
    exact (h1.mul h2).mul h3
  have hfin : ∫⁻ p, ENNReal.ofReal (w p.1 * K p.1 p.2 * F p.2) ∂(μ.prod ν) < ⊤ := by
    have hcongr :
        ∫⁻ p, ENNReal.ofReal (w p.1 * K p.1 p.2 * F p.2) ∂(μ.prod ν)
          = ∫⁻ p, (ENNReal.ofReal (w p.1) * ENNReal.ofReal (K p.1 p.2) * ENNReal.ofReal (F p.2))
              ∂(μ.prod ν) := by
      apply lintegral_congr; intro p
      rw [ENNReal.ofReal_mul (mul_nonneg (hw0 p.1) (hK0 p.1 p.2)), ENNReal.ofReal_mul (hw0 p.1)]
    rw [hcongr]
    have hRtop : ENNReal.ofReal C * ENNReal.ofReal M ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
    calc ∫⁻ p, (ENNReal.ofReal (w p.1) * ENNReal.ofReal (K p.1 p.2) * ENNReal.ofReal (F p.2))
            ∂(μ.prod ν)
        = ∫⁻ a, ∫⁻ b, (ENNReal.ofReal (w a) * ENNReal.ofReal (K a b) * ENNReal.ofReal (F b))
            ∂ν ∂μ := by
          rw [lintegral_prod _ hGa]
      _ ≤ ∫⁻ a, ENNReal.ofReal (w a) * (ENNReal.ofReal C * ENNReal.ofReal M) ∂μ := by
          apply lintegral_mono; intro a
          calc ∫⁻ b, (ENNReal.ofReal (w a) * ENNReal.ofReal (K a b) * ENNReal.ofReal (F b)) ∂ν
              ≤ ∫⁻ b, (ENNReal.ofReal (w a) * ENNReal.ofReal (K a b) * ENNReal.ofReal M) ∂ν :=
                lintegral_mono (fun b =>
                  mul_le_mul_right (ENNReal.ofReal_le_ofReal (hM b))
                    (ENNReal.ofReal (w a) * ENNReal.ofReal (K a b)))
            _ = (∫⁻ b, ENNReal.ofReal (w a) * ENNReal.ofReal (K a b) ∂ν) * ENNReal.ofReal M := by
                rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
            _ = (ENNReal.ofReal (w a) * ∫⁻ b, ENNReal.ofReal (K a b) ∂ν) * ENNReal.ofReal M := by
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            _ ≤ (ENNReal.ofReal (w a) * ENNReal.ofReal C) * ENNReal.ofReal M := by
                exact mul_le_mul_left (mul_le_mul_right (hC a) (ENNReal.ofReal (w a))) (ENNReal.ofReal M)
            _ = ENNReal.ofReal (w a) * (ENNReal.ofReal C * ENNReal.ofReal M) := by rw [mul_assoc]
      _ = (∫⁻ a, ENNReal.ofReal (w a) ∂μ) * (ENNReal.ofReal C * ENNReal.ofReal M) := by
          rw [lintegral_mul_const' _ _ hRtop]
      _ = ENNReal.ofReal (∫ a, w a ∂μ) * (ENNReal.ofReal C * ENNReal.ofReal M) := by
          rw [ofReal_integral_eq_lintegral_ofReal hw (Filter.Eventually.of_forall hw0)]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
                (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hHas : HasFiniteIntegral (fun p : α × β => w p.1 * K p.1 p.2 * F p.2) (μ.prod ν) := by
    rw [hasFiniteIntegral_iff_norm]
    refine lt_of_eq_of_lt ?_ hfin
    apply lintegral_congr; intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hw0 p.1) (hK0 p.1 p.2)) (hF0 p.2))]
  have hInt : Integrable (fun p : α × β => w p.1 * K p.1 p.2 * F p.2) (μ.prod ν) :=
    ⟨hfa.aestronglyMeasurable, hHas⟩
  refine ⟨hInt, ?_⟩
  rw [integral_prod (f := fun p : α × β => w p.1 * K p.1 p.2 * F p.2) hInt,
      integral_integral_swap (f := fun a b => w a * K a b * F b) hInt]
  apply integral_congr_ae
  filter_upwards with b
  rw [integral_mul_const (F b) (fun a => w a * K a b)]
  exact mul_comm _ _

end Commons.Measure.Integral