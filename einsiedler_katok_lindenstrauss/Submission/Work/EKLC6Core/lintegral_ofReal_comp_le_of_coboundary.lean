import Mathlib
import Submission.Work.EKLC6Core.coboundary_integral
import Submission.Work.EKLC6Core.lintegral_ofReal_sub_comp_le

namespace Work.EKLC6Core

/-- **Coboundary inequality for the lintegral.**

If `a = ψ ∘ T - ψ + g ∘ T` almost everywhere, with `a` integrable and `a, g ≥ 0` a.e. and `T`
measure preserving on a probability space, then `∫⁻ ofReal (g ∘ T) ≤ ∫⁻ ofReal a`.

The proof reduces to `Work.EKLC6Core.lintegral_ofReal_sub_comp_le` applied to a measurable
representative `u` of `ψ`: writing `f := u ∘ T - u`, the identity gives `g ∘ T = a - f` a.e.,
so `a - f = (a - f⁺) + f⁻`, and
`∫⁻ ofReal (g ∘ T) = ofReal (∫ a - ∫ f⁺) + ∫⁻ ofReal (f⁻) ≤ ofReal (∫ a - ∫ f⁺) + ofReal (∫ f⁺)
= ofReal (∫ a) = ∫⁻ ofReal a`. -/
theorem lintegral_ofReal_comp_le_of_coboundary {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasureTheory.MeasurePreserving T μ μ)
    {a ψ g : X → ℝ} (ha_int : MeasureTheory.Integrable a μ) (ha_nn : 0 ≤ᵐ[μ] a)
    (hψ : AEMeasurable ψ μ) (hgnn : 0 ≤ᵐ[μ] g)
    (hid : ∀ᵐ x ∂μ, a x = ψ (T x) - ψ x + g (T x)) :
    ∫⁻ x, ENNReal.ofReal (g (T x)) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (a x) ∂μ := by
  classical
  let u : X → ℝ := AEMeasurable.mk ψ hψ
  have hu_meas : Measurable u := hψ.measurable_mk
  have hu_eq : ψ =ᵐ[μ] u := hψ.ae_eq_mk
  have huT_eq : ψ ∘ T =ᵐ[μ] u ∘ T := hT.quasiMeasurePreserving.ae_eq_comp hu_eq
  have hidu : ∀ᵐ x ∂μ, a x = u (T x) - u x + g (T x) := by
    filter_upwards [hid, hu_eq, huT_eq] with x hx hux huTx
    simp only [Function.comp_apply] at huTx
    rw [hx, hux, huTx]
  have hGnn : 0 ≤ᵐ[μ] fun x => g (T x) :=
    hT.quasiMeasurePreserving.tendsto_ae.eventually hgnn
  let f : X → ℝ := fun x => u (T x) - u x
  have hf_meas : Measurable f := (hu_meas.comp hT.measurable).sub hu_meas
  have haf : ∀ᵐ x ∂μ, a x = f x + g (T x) := by
    filter_upwards [hidu] with x hx
    rw [hx]
  have hfa : ∀ᵐ x ∂μ, f x ≤ a x := by
    filter_upwards [haf, hGnn] with x hx hg
    simp only [Pi.zero_apply] at hg
    rw [hx]; linarith
  let fp : X → ℝ := fun x => max (f x) 0
  let fm : X → ℝ := fun x => max (-(f x)) 0
  have hfp_meas : Measurable fp := hf_meas.max measurable_const
  have hfm_meas : Measurable fm := hf_meas.neg.max measurable_const
  have hfp_le_a : ∀ᵐ x ∂μ, fp x ≤ a x := by
    filter_upwards [hfa, ha_nn] with x hx ha
    exact max_le hx ha
  have hfp_int : MeasureTheory.Integrable fp μ :=
    ha_int.mono' hfp_meas.aestronglyMeasurable (by
      filter_upwards [hfp_le_a] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right (f x) 0)]
      exact hx)
  have hfp_nn : 0 ≤ᵐ[μ] fp := Filter.Eventually.of_forall fun x => le_max_right (f x) 0
  have hlint_a : ∫⁻ x, ENNReal.ofReal (a x) ∂μ = ENNReal.ofReal (∫ x, a x ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ha_int ha_nn).symm
  have hfin : ∫⁻ x, ENNReal.ofReal (u (T x) - u x) ∂μ < ⊤ := by
    have h1 : ∫⁻ x, ENNReal.ofReal (u (T x) - u x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (a x) ∂μ := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [hfa] with x hx
      exact ENNReal.ofReal_le_ofReal (by simpa only [f] using hx)
    rw [hlint_a] at h1
    exact lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  have hA := lintegral_ofReal_sub_comp_le hT hu_meas hfin
  have hfm_eq : ∫⁻ x, ENNReal.ofReal (fm x) ∂μ = ∫⁻ x, ENNReal.ofReal (u x - u (T x)) ∂μ := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with x
    have hxx : fm x = max (u x - u (T x)) 0 := by
      show max (-(u (T x) - u x)) 0 = max (u x - u (T x)) 0
      rw [show -(u (T x) - u x) = u x - u (T x) by ring]
    rw [hxx, ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact max_eq_left bot_le
  have hfp_eq : ∫⁻ x, ENNReal.ofReal (fp x) ∂μ = ∫⁻ x, ENNReal.ofReal (u (T x) - u x) ∂μ := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards with x
    have hxx : fp x = max (u (T x) - u x) 0 := rfl
    rw [hxx, ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact max_eq_left bot_le
  have hfm_le_fp : ∫⁻ x, ENNReal.ofReal (fm x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (fp x) ∂μ := by
    rw [hfm_eq, hfp_eq]; exact hA
  have hfp_lin : ∫⁻ x, ENNReal.ofReal (fp x) ∂μ = ENNReal.ofReal (∫ x, fp x ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfp_int hfp_nn).symm
  have hafp_int : MeasureTheory.Integrable (fun x => a x - fp x) μ := ha_int.sub hfp_int
  have hafp_nn : 0 ≤ᵐ[μ] fun x => a x - fp x := by
    filter_upwards [hfp_le_a] with x hx
    show (0:ℝ) ≤ a x - fp x
    linarith
  have hlint_afp : ∫⁻ x, ENNReal.ofReal (a x - fp x) ∂μ
      = ENNReal.ofReal (∫ x, (a x - fp x) ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hafp_int hafp_nn).symm
  have hG_decomp : ∀ᵐ x ∂μ, ENNReal.ofReal (g (T x))
      = ENNReal.ofReal (a x - fp x) + ENNReal.ofReal (fm x) := by
    filter_upwards [haf, hfp_le_a] with x hx hfp_a
    have hg_eq : g (T x) = a x - f x := by linarith [hx]
    have hs : f x = fp x - fm x := by
      show f x = max (f x) 0 - max (-(f x)) 0
      rcases le_total (f x) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -(f x))]; ring
      · rw [max_eq_left h, max_eq_right (by linarith : -(f x) ≤ 0)]; ring
    have hpos : (0:ℝ) ≤ a x - fp x := by linarith [hfp_a]
    have hfmx : (0:ℝ) ≤ fm x := le_max_right (-(f x)) 0
    rw [hg_eq, show a x - f x = (a x - fp x) + fm x by rw [hs]; ring,
        ENNReal.ofReal_add hpos hfmx]
  have hfst_ae : AEMeasurable (fun x => ENNReal.ofReal (a x - fp x)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (ha_int.aemeasurable.sub hfp_meas.aemeasurable)
  calc ∫⁻ x, ENNReal.ofReal (g (T x)) ∂μ
      = ∫⁻ x, (ENNReal.ofReal (a x - fp x) + ENNReal.ofReal (fm x)) ∂μ :=
          MeasureTheory.lintegral_congr_ae hG_decomp
    _ = ∫⁻ x, ENNReal.ofReal (a x - fp x) ∂μ + ∫⁻ x, ENNReal.ofReal (fm x) ∂μ :=
          MeasureTheory.lintegral_add_left' hfst_ae _
    _ ≤ ∫⁻ x, ENNReal.ofReal (a x - fp x) ∂μ + ∫⁻ x, ENNReal.ofReal (fp x) ∂μ :=
          add_le_add le_rfl hfm_le_fp
    _ = ENNReal.ofReal (∫ x, (a x - fp x) ∂μ) + ENNReal.ofReal (∫ x, fp x ∂μ) := by
          rw [hlint_afp, hfp_lin]
    _ = ENNReal.ofReal (∫ x, a x ∂μ) := by
          rw [MeasureTheory.integral_sub ha_int hfp_int]
          have hB : (0:ℝ) ≤ ∫ x, fp x ∂μ := MeasureTheory.integral_nonneg_of_ae hfp_nn
          have hBA : ∫ x, fp x ∂μ ≤ ∫ x, a x ∂μ :=
            MeasureTheory.integral_mono_ae hfp_int ha_int hfp_le_a
          rw [ENNReal.ofReal_sub _ hB]
          exact tsub_add_cancel_of_le (ENNReal.ofReal_le_ofReal hBA)
    _ = ∫⁻ x, ENNReal.ofReal (a x) ∂μ := hlint_a.symm

end Work.EKLC6Core
