import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the logarithmic-window average of an `L¹` datum

For `δ > 0` and `γ ∈ L¹((0,∞))` with `γ ≥ 0`, the function

`z ↦ ∫ t, 1_{|log z - t| ≤ δ} γ (e^t) dt`

is integrable on `(0,∞)`.

This is the `L¹`-analogue of the radial Schur test `zSchur`: after the substitution `t = log y`
the window `|log z - t| ≤ δ` becomes the multiplicative window `z e^{-δ} ≤ y ≤ z e^{δ}`, and

`∫_{z>0} ∫ t, 1_{|log z - t| ≤ δ} γ (e^t) dt dz = ∫_{|u| ≤ δ} e^{-u} du · ∫_{y>0} γ y dy`

by Tonelli (everything is nonnegative).  The proof is carried out in the logarithmic variable
`w = log z`, where the statement becomes

`∫⁻ w, ofReal (e^w * ∫ t, 1_{|w - t| ≤ δ} h t) ≤ ofReal (2 δ e^δ) * ∫⁻ t, ofReal (e^t h t)`

for `h = γ ∘ exp` (`lintegral_main`), using Tonelli and the elementary window estimate
`lintegral_window_le`.
-/

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set Filter

/-- The measure of the window `{w : |w - t| ≤ δ}` against the weight `e^w`: this is the
logarithmic Schur test for the *indicator* of the window. -/
private lemma lintegral_window_le (δ t : ℝ) :
    ∫⁻ w : ℝ, (if |w - t| ≤ δ then ENNReal.ofReal (Real.exp w) else 0)
      ≤ ENNReal.ofReal (Real.exp (t + δ)) * ENNReal.ofReal (2 * δ) := by
  have hset : MeasurableSet {w : ℝ | |w - t| ≤ δ} :=
    measurableSet_le ((continuous_abs.comp (continuous_id.sub continuous_const)).measurable)
      measurable_const
  have h1 : (∫⁻ w : ℝ, (if |w - t| ≤ δ then ENNReal.ofReal (Real.exp w) else 0))
      = ∫⁻ w : ℝ, {w : ℝ | |w - t| ≤ δ}.indicator (fun w => ENNReal.ofReal (Real.exp w)) w := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    by_cases h : |w - t| ≤ δ <;> simp [Set.indicator, h]
  rw [h1, MeasureTheory.lintegral_indicator hset (fun w : ℝ => ENNReal.ofReal (Real.exp w))]
  have hseteq : {w : ℝ | |w - t| ≤ δ} = Set.Icc (t - δ) (t + δ) := by
    ext w
    rw [Set.mem_ofPred_eq, abs_le]
    constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hseteq]
  have hmono : ∫⁻ w in Set.Icc (t - δ) (t + δ), ENNReal.ofReal (Real.exp w)
      ≤ ∫⁻ w in Set.Icc (t - δ) (t + δ), ENNReal.ofReal (Real.exp (t + δ)) := by
    refine MeasureTheory.setLIntegral_mono measurable_const (fun w hw => ?_)
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hw.2)
  refine le_trans hmono (le_of_eq ?_)
  rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
  rw [show (t + δ) - (t - δ) = 2 * δ by ring]

/-- The slice bound for fixed `t`: pulling the constant `ofReal (h t)` out of the `w`-integral
and applying `lintegral_window_le`. -/
private lemma lintegral_slice_le {δ t : ℝ} {h : ℝ → ℝ} :
    ∫⁻ w : ℝ, ENNReal.ofReal (Real.exp w * (if |w - t| ≤ δ then h t else 0))
      ≤ ENNReal.ofReal (Real.exp (t + δ)) * ENNReal.ofReal (2 * δ) * ENNReal.ofReal (h t) := by
  have hGm : Measurable (fun w : ℝ => if |w - t| ≤ δ then ENNReal.ofReal (Real.exp w) else 0) := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_le ((continuous_abs.comp (continuous_id.sub continuous_const)).measurable)
        measurable_const
    · exact Real.measurable_exp.ennreal_ofReal
  have hpt : ∀ w : ℝ, ENNReal.ofReal (Real.exp w * (if |w - t| ≤ δ then h t else 0))
      = ENNReal.ofReal (h t) * (if |w - t| ≤ δ then ENNReal.ofReal (Real.exp w) else 0) := by
    intro w
    by_cases hc : |w - t| ≤ δ
    · simp only [hc, ite_true]
      rw [ENNReal.ofReal_mul (Real.exp_pos w).le, mul_comm]
    · simp only [hc, ite_false, mul_zero, ENNReal.ofReal_zero]
  calc ∫⁻ w : ℝ, ENNReal.ofReal (Real.exp w * (if |w - t| ≤ δ then h t else 0))
      = ∫⁻ w : ℝ, ENNReal.ofReal (h t)
          * (if |w - t| ≤ δ then ENNReal.ofReal (Real.exp w) else 0) :=
        lintegral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ENNReal.ofReal (h t)
          * ∫⁻ w : ℝ, (if |w - t| ≤ δ then ENNReal.ofReal (Real.exp w) else 0) :=
        MeasureTheory.lintegral_const_mul'' _ hGm.aemeasurable
    _ ≤ ENNReal.ofReal (h t) * (ENNReal.ofReal (Real.exp (t + δ)) * ENNReal.ofReal (2 * δ)) :=
        mul_le_mul_of_nonneg_left (lintegral_window_le δ t) (by simp)
    _ = ENNReal.ofReal (Real.exp (t + δ)) * ENNReal.ofReal (2 * δ) * ENNReal.ofReal (h t) := by
        ring

/-- **The lintegral computation.**  For nonnegative a.e. measurable `h`,

`∫⁻ w, ofReal (e^w ∫ t, 1_{|w - t| ≤ δ} h t) ≤ ofReal (2 δ e^δ) · ∫⁻ t, ofReal (e^t h t)`.

The weight `e^w` on the left is exactly the Jacobian of the substitution `w = log z`; it is what
makes the estimate true without any decay assumption on `h` itself. -/
private lemma lintegral_main {δ : ℝ} (hδ : 0 < δ) {h : ℝ → ℝ} (hm : AEMeasurable h volume)
    (hnn : 0 ≤ h) :
    ∫⁻ w : ℝ, ENNReal.ofReal (Real.exp w * ∫ t : ℝ, (if |w - t| ≤ δ then h t else 0))
      ≤ ENNReal.ofReal (2 * δ * Real.exp δ) * ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t * h t) := by
  -- Step 1: the pointwise bound of the slice integral by its lintegral
  have hslice : ∀ w : ℝ,
      ENNReal.ofReal (Real.exp w * ∫ t : ℝ, (if |w - t| ≤ δ then h t else 0))
        ≤ ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp w * (if |w - t| ≤ δ then h t else 0)) := by
    intro w
    have hset : MeasurableSet {t : ℝ | |w - t| ≤ δ} :=
      measurableSet_le ((continuous_abs.comp (continuous_const.sub continuous_id)).measurable)
        measurable_const
    have hite : Measurable (fun t : ℝ => if |w - t| ≤ δ then (1 : ℝ) else 0) :=
      Measurable.ite hset measurable_const measurable_const
    have haesm : AEMeasurable (fun t : ℝ => (if |w - t| ≤ δ then h t else 0)) volume := by
      have h2 : AEMeasurable (fun t : ℝ => (if |w - t| ≤ δ then (1 : ℝ) else 0) * h t) volume :=
        hite.aemeasurable.mul hm
      refine h2.congr (Filter.Eventually.of_forall (fun t => ?_))
      by_cases hc : |w - t| ≤ δ <;> simp [hc]
    have hA : ENNReal.ofReal (∫ t, (if |w - t| ≤ δ then h t else 0))
        ≤ ∫⁻ t, ENNReal.ofReal (if |w - t| ≤ δ then h t else 0) := by
      by_cases hint : Integrable (fun t => (if |w - t| ≤ δ then h t else 0)) volume
      · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall (fun t => by
            simp only []
            split_ifs with ht
            · exact hnn t
            · exact le_refl 0))]
      · rw [MeasureTheory.integral_undef hint]; simp
    calc ENNReal.ofReal (Real.exp w * ∫ t, (if |w - t| ≤ δ then h t else 0))
        = ENNReal.ofReal (Real.exp w)
            * ENNReal.ofReal (∫ t, (if |w - t| ≤ δ then h t else 0)) :=
          ENNReal.ofReal_mul (Real.exp_pos w).le
      _ ≤ ENNReal.ofReal (Real.exp w)
            * ∫⁻ t, ENNReal.ofReal (if |w - t| ≤ δ then h t else 0) :=
          mul_le_mul_of_nonneg_left hA (by simp)
      _ = ∫⁻ t, ENNReal.ofReal (Real.exp w)
            * ENNReal.ofReal (if |w - t| ≤ δ then h t else 0) :=
          (MeasureTheory.lintegral_const_mul'' _ haesm.ennreal_ofReal).symm
      _ = ∫⁻ t, ENNReal.ofReal (Real.exp w * (if |w - t| ≤ δ then h t else 0)) :=
          lintegral_congr_ae (Filter.Eventually.of_forall (fun t =>
            (ENNReal.ofReal_mul (Real.exp_pos w).le).symm))
  -- Step 2: Tonelli
  have hton : ∫⁻ w : ℝ, (∫⁻ t : ℝ,
        ENNReal.ofReal (Real.exp w * (if |w - t| ≤ δ then h t else 0)))
      = ∫⁻ t : ℝ, (∫⁻ w : ℝ,
        ENNReal.ofReal (Real.exp w * (if |w - t| ≤ δ then h t else 0))) := by
    refine MeasureTheory.lintegral_lintegral_swap ?_
    have h1 : Measurable (fun p : ℝ × ℝ => (if |p.1 - p.2| ≤ δ then (1 : ℝ) else 0)) := by
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_le
        ((continuous_abs.comp (continuous_fst.sub continuous_snd)).measurable) measurable_const
    have h2 : AEMeasurable (fun p : ℝ × ℝ => h p.2) (volume.prod volume) :=
      AEMeasurable.comp_snd hm
    have h3 : AEMeasurable (fun p : ℝ × ℝ => (if |p.1 - p.2| ≤ δ then h p.2 else 0))
        (volume.prod volume) := by
      refine (h1.aemeasurable.mul h2).congr (Filter.Eventually.of_forall (fun p => ?_))
      by_cases hc : |p.1 - p.2| ≤ δ <;> simp [hc]
    have h4 : AEMeasurable (fun p : ℝ × ℝ =>
        Real.exp p.1 * (if |p.1 - p.2| ≤ δ then h p.2 else 0)) (volume.prod volume) :=
      (Real.measurable_exp.comp measurable_fst).aemeasurable.mul h3
    exact h4.ennreal_ofReal
  -- Step 3: reassociate the constant
  have hconst : ∀ t : ℝ, ENNReal.ofReal (Real.exp (t + δ)) * ENNReal.ofReal (2 * δ)
        * ENNReal.ofReal (h t)
      = ENNReal.ofReal (2 * δ * Real.exp δ) * ENNReal.ofReal (Real.exp t * h t) := by
    intro t
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos t).le,
      ENNReal.ofReal_mul (Real.exp_pos t).le]
    rw [show ENNReal.ofReal (2 * δ * Real.exp δ)
        = ENNReal.ofReal (2 * δ) * ENNReal.ofReal (Real.exp δ) from
      ENNReal.ofReal_mul (le_of_lt (mul_pos two_pos hδ))]
    ring
  calc ∫⁻ w : ℝ, ENNReal.ofReal (Real.exp w * ∫ t : ℝ, (if |w - t| ≤ δ then h t else 0))
      ≤ ∫⁻ w : ℝ, (∫⁻ t : ℝ,
          ENNReal.ofReal (Real.exp w * (if |w - t| ≤ δ then h t else 0))) :=
        lintegral_mono hslice
    _ = ∫⁻ t : ℝ, (∫⁻ w : ℝ,
          ENNReal.ofReal (Real.exp w * (if |w - t| ≤ δ then h t else 0))) := hton
    _ ≤ ∫⁻ t : ℝ,
          ENNReal.ofReal (2 * δ * Real.exp δ) * ENNReal.ofReal (Real.exp t * h t) := by
        refine lintegral_mono (fun t => ?_)
        exact le_trans (lintegral_slice_le (h := h)) (le_of_eq (hconst t))
    _ = ENNReal.ofReal (2 * δ * Real.exp δ)
          * ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t * h t) :=
        MeasureTheory.lintegral_const_mul'' _
          ((Real.measurable_exp.aemeasurable.mul hm).ennreal_ofReal)

/-- The logarithmic form of the target: if `h` is a.e. measurable, nonnegative and such that
`t ↦ e^t h t` is integrable, then `w ↦ e^w ∫ t, 1_{|w - t| ≤ δ} h t` is integrable. -/
private lemma integrable_logConvolution {δ : ℝ} (hδ : 0 < δ) {h : ℝ → ℝ}
    (hm : AEMeasurable h volume) (hnn : 0 ≤ h)
    (hint : Integrable (fun t : ℝ => Real.exp t * h t) volume) :
    Integrable (fun w : ℝ => Real.exp w * ∫ t : ℝ, (if |w - t| ≤ δ then h t else 0)) volume := by
  -- measurability
  have hmeas : AEStronglyMeasurable
      (fun w : ℝ => Real.exp w * ∫ t : ℝ, (if |w - t| ≤ δ then h t else 0)) volume := by
    have hJ : AEStronglyMeasurable
        (fun w : ℝ => ∫ t : ℝ, (if |w - t| ≤ δ then h t else 0)) volume := by
      have h1 : Measurable (fun p : ℝ × ℝ => (if |p.1 - p.2| ≤ δ then (1 : ℝ) else 0)) := by
        refine Measurable.ite ?_ measurable_const measurable_const
        exact measurableSet_le
          ((continuous_abs.comp (continuous_fst.sub continuous_snd)).measurable) measurable_const
      have h2 : AEMeasurable (fun p : ℝ × ℝ => h p.2) (volume.prod volume) :=
        AEMeasurable.comp_snd hm
      have hK : AEStronglyMeasurable
          (fun p : ℝ × ℝ => (if |p.1 - p.2| ≤ δ then (1 : ℝ) else 0) * h p.2)
          (volume.prod volume) :=
        (h1.aemeasurable.mul h2).aestronglyMeasurable
      refine (MeasureTheory.AEStronglyMeasurable.integral_prod_right' hK).congr
        (Filter.Eventually.of_forall (fun w => ?_))
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      by_cases hc : |w - t| ≤ δ <;> simp [hc]
    exact Real.continuous_exp.aestronglyMeasurable.mul hJ
  refine ⟨hmeas, ?_⟩
  have hHnn : 0 ≤ fun w : ℝ => Real.exp w * ∫ t : ℝ, (if |w - t| ≤ δ then h t else 0) := by
    intro w
    refine mul_nonneg (Real.exp_pos w).le (integral_nonneg (fun t => ?_))
    simp only [Pi.zero_apply]
    split_ifs with ht
    · exact hnn t
    · exact le_refl 0
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hHnn)]
  have hlin : ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t * h t) < ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun t => mul_nonneg (Real.exp_pos t).le (hnn t)))]
    exact ENNReal.ofReal_lt_top
  exact lt_of_le_of_lt (lintegral_main hδ hm hnn)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlin)

theorem indicatorLog_integrable {δ : ℝ} (hδ : 0 < δ) {γ : ℝ → ℝ}
    (hγ : MeasureTheory.IntegrableOn γ (Set.Ioi 0)) (hγnn : 0 ≤ γ) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ t : ℝ, (if |Real.log z - t| ≤ δ then γ (Real.exp t) else 0))
      (Set.Ioi 0) := by
  set h : ℝ → ℝ := fun t => γ (Real.exp t) with hh
  have hgm : AEStronglyMeasurable (fun t : ℝ => γ (Real.exp t)) volume := by
    have h1 : Integrable (fun x : ℝ => Real.exp x • γ (Real.exp x)) volume :=
      (MeasureTheory.integrable_comp_exp γ).mpr hγ
    have h2 : AEStronglyMeasurable (fun x : ℝ => Real.exp x * γ (Real.exp x)) volume := by
      simpa only [smul_eq_mul] using h1.aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun x : ℝ => (Real.exp x)⁻¹) volume := by fun_prop
    have h4 : AEStronglyMeasurable
        (fun x : ℝ => (Real.exp x * γ (Real.exp x)) * (Real.exp x)⁻¹) volume := h2.mul h3
    refine h4.congr (Filter.Eventually.of_forall (fun x => ?_))
    have hx : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
    field_simp
  have hm : AEMeasurable h volume := by
    refine hgm.aemeasurable.congr (Filter.Eventually.of_forall (fun t => ?_))
    rw [hh]
  have hnn : 0 ≤ h := by
    intro t
    rw [hh]
    exact hγnn (Real.exp t)
  have hint : Integrable (fun t : ℝ => Real.exp t * h t) volume := by
    have h1 : Integrable (fun x : ℝ => Real.exp x • γ (Real.exp x)) volume :=
      (MeasureTheory.integrable_comp_exp γ).mpr hγ
    simpa only [hh, smul_eq_mul] using h1
  have hInt := integrable_logConvolution hδ hm hnn hint
  rw [← MeasureTheory.integrable_comp_exp
    (fun z : ℝ => ∫ t : ℝ, (if |Real.log z - t| ≤ δ then γ (Real.exp t) else 0))]
  refine hInt.congr (Filter.Eventually.of_forall (fun w => ?_))
  simp only [hh, smul_eq_mul, Real.log_exp]

end Work.FTS.EllSol.EllPkgAux.MollDom
