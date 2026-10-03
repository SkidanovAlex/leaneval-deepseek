import Mathlib

open MeasureTheory

namespace Work.FIChain

/-- Boundedness + measurability of `F` make `σ ↦ F σ / σ` interval integrable on any
interval whose left endpoint is positive. -/
private lemma intervalIntegrable_div_of_le {F : ℝ → ℝ} (hFmeas : Measurable F) {K a b : ℝ}
    (hFbd : ∀ σ : ℝ, |F σ| ≤ K) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun σ : ℝ => F σ / σ) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hK : 0 ≤ K := le_trans (abs_nonneg (F 0)) (hFbd 0)
  refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ (K / a) ?_
  · exact (hFmeas.div measurable_id).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx0 : 0 < x := lt_of_lt_of_le ha (le_of_lt hx.1)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0]
    exact div_le_div₀ hK (hFbd x) ha (le_of_lt hx.1)

/-- Shifting the integration range of `∫ F σ / σ` down by a factor `d ≥ 1` does not
increase the integral, provided `F` vanishes on `σ < 1` and is nonnegative.

Indeed, with `f σ = F σ / σ`, monotonicity of the integral gives
`∫_{1/d}^{C/d} f ≤ ∫_{1/d}^{C} f`, and splitting the latter at `1` gives
`∫_{1/d}^{C} f = ∫_{1/d}^{1} f + ∫_1^C f = ∫_1^C f`, since `f` vanishes a.e. on
`(1/d, 1]` (there `σ ≤ 1`, so `F σ = 0` except possibly at the single point `σ = 1`). -/
theorem RhoWin2ShiftRange (F : ℝ → ℝ) (d C K : ℝ) (hFmeas : Measurable F)
    (hFbd : ∀ σ : ℝ, |F σ| ≤ K) (hFnn : ∀ σ : ℝ, 0 ≤ F σ) (hF0 : ∀ σ : ℝ, σ < 1 → F σ = 0)
    (hd : 1 ≤ d) (hC1 : 1 ≤ C) :
    (∫ σ in (1 / d)..(C / d), F σ / σ) ≤ ∫ σ in (1 : ℝ)..C, F σ / σ := by
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hd
  have h1d_pos : 0 < 1 / d := by positivity
  have h1d_le_one : 1 / d ≤ 1 := by rw [div_le_one hd0]; exact hd
  have h1d_le_C : 1 / d ≤ C := le_trans h1d_le_one hC1
  have hCd : 1 / d ≤ C / d := by gcongr
  have hCdC : C / d ≤ C := by
    rw [div_le_iff₀ hd0]
    nlinarith
  set f : ℝ → ℝ := fun σ => F σ / σ with hf_def
  have hfnn' : 0 ≤ᵐ[volume.restrict (Set.Ioc (1 / d) C)] f := by
    rw [hf_def]
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall
      (fun x hx => div_nonneg (hFnn x) (le_of_lt (lt_of_lt_of_le h1d_pos (le_of_lt hx.1)))))
  have hInt : IntervalIntegrable f volume (1 / d) C := by
    rw [hf_def]
    exact intervalIntegrable_div_of_le hFmeas hFbd h1d_pos h1d_le_C
  have hA : IntervalIntegrable f volume (1 / d) 1 := by
    rw [hf_def]
    exact intervalIntegrable_div_of_le hFmeas hFbd h1d_pos h1d_le_one
  have hB : IntervalIntegrable f volume (1 : ℝ) C := by
    rw [hf_def]
    exact intervalIntegrable_div_of_le hFmeas hFbd zero_lt_one hC1
  have hmain : (∫ σ in (1 / d)..(C / d), f σ) ≤ ∫ σ in (1 / d)..C, f σ :=
    intervalIntegral.integral_mono_interval le_rfl hCd hCdC hfnn' hInt
  have hadj : (∫ σ in (1 / d)..1, f σ) + ∫ σ in (1 : ℝ)..C, f σ = ∫ σ in (1 / d)..C, f σ :=
    intervalIntegral.integral_add_adjacent_intervals hA hB
  have hzero : (∫ σ in (1 / d)..1, f σ) = 0 := by
    rw [hf_def, intervalIntegral.integral_of_le h1d_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by
      simp [hF0 x hx.2])
  calc (∫ σ in (1 / d)..(C / d), f σ) ≤ ∫ σ in (1 / d)..C, f σ := hmain
    _ = (∫ σ in (1 / d)..1, f σ) + ∫ σ in (1 : ℝ)..C, f σ := hadj.symm
    _ = ∫ σ in (1 : ℝ)..C, f σ := by rw [hzero, zero_add]

end Work.FIChain
