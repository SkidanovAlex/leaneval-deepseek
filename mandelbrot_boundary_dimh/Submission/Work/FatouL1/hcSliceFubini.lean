import Mathlib

/-!
# Fubini for holomorphic functions of bounded `L¹`-mass on a vertical strip

For `h` holomorphic on the open vertical strip `{z | a < z.re ∧ z.re < b}` whose every vertical
line has `L¹`-mass at most `m`, the function

`Y ↦ ∫ x in x₁..x₂, ‖h (x + Y*I)‖`

is continuous on `ℝ`, and its integral over any interval `[Y₁, Y₂]` is at most
`(x₂ - x₁) * max m 0`.

The continuity is dominated convergence with a locally uniform bound coming from compactness of
the slice inside the (open) strip.  The bound is Tonelli: swap the two nonnegative integrals, bound
the horizontal line mass by the full vertical line mass (`hmass`) and integrate the constant.
-/

namespace Work.FatouL1

open MeasureTheory Set Filter
open scoped Topology ENNReal

set_option linter.unusedVariables false in
theorem hcSliceFubini {a b m : ℝ} {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b, ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Set.Ioo a b) (h₂ : x₂ ∈ Set.Ioo a b) (h12 : x₁ < x₂) :
    Continuous (fun Y : ℝ => ∫ x : ℝ in x₁..x₂, ‖h ((x : ℂ) + Y * Complex.I)‖) ∧
    (∀ Y₁ Y₂ : ℝ, Y₁ ≤ Y₂ →
      ∫ Y : ℝ in Y₁..Y₂, (∫ x : ℝ in x₁..x₂, ‖h ((x : ℂ) + Y * Complex.I)‖)
        ≤ (x₂ - x₁) * max m 0) := by
  have hx12 : x₁ ≤ x₂ := h12.le
  -- ## Global continuity of the parametrised integral
  have hcont : Continuous (fun Y : ℝ => ∫ x : ℝ in x₁..x₂, ‖h ((x : ℂ) + Y * Complex.I)‖) := by
    have hstrip : ContinuousOn h {z : ℂ | a < z.re ∧ z.re < b} := hhol.continuousOn
    have hopen : IsOpen {z : ℂ | a < z.re ∧ z.re < b} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hlo : a < min x₁ x₂ := lt_min h₁.1 h₂.1
    have hhi : max x₁ x₂ < b := max_lt h₁.2 h₂.2
    rw [continuous_iff_continuousAt]
    intro Y₀
    have hrect : ContinuousOn (fun q : ℝ × ℝ => h ((q.2 : ℂ) + q.1 * Complex.I))
        (Set.Icc (Y₀ - 1) (Y₀ + 1) ×ˢ Set.Icc (min x₁ x₂) (max x₁ x₂)) := by
      have hmaps : MapsTo (fun q : ℝ × ℝ => ((q.2 : ℂ) + q.1 * Complex.I))
          (Set.Icc (Y₀ - 1) (Y₀ + 1) ×ˢ Set.Icc (min x₁ x₂) (max x₁ x₂))
          {z : ℂ | a < z.re ∧ z.re < b} := by
        intro q hq
        simp only [Set.mem_prod, Set.mem_Icc] at hq
        simp only [Set.mem_ofPred_eq]
        have hre : ((q.2 : ℂ) + q.1 * Complex.I).re = q.2 := by simp
        rw [hre]
        exact ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
      exact hstrip.comp (by fun_prop) hmaps
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hrect
    refine intervalIntegral.continuousAt_of_dominated_interval
      (F := fun (Y x : ℝ) => ‖h ((x : ℂ) + (Y : ℂ) * Complex.I)‖) (x₀ := Y₀)
      (bound := fun _ => C) (a := x₁) (b := x₂) ?_ ?_ ?_ ?_
    · filter_upwards with Y
      have hmaps : MapsTo (fun x : ℝ => ((x : ℂ) + (Y : ℂ) * Complex.I)) (Set.uIoc x₁ x₂)
          {z : ℂ | a < z.re ∧ z.re < b} := by
        intro x hx
        rw [Set.mem_uIoc] at hx
        simp only [Set.mem_ofPred_eq]
        have hre : ((x : ℂ) + (Y : ℂ) * Complex.I).re = x := by simp
        rw [hre]
        rcases hx with ⟨hx1, hx2⟩ | ⟨hx2, hx1⟩
        · exact ⟨by linarith [h₁.1, hx1], by linarith [h₂.2, hx2]⟩
        · exact ⟨by linarith [h₂.1, hx2], by linarith [h₁.2, hx1]⟩
      exact (hstrip.comp (by fun_prop) hmaps).norm.aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [Ioo_mem_nhds (by linarith : Y₀ - 1 < Y₀) (by linarith : Y₀ < Y₀ + 1)]
        with Y hY
      filter_upwards with x hx
      have hxle : x ∈ Set.Icc (min x₁ x₂) (max x₁ x₂) := by
        have := Set.uIoc_subset_uIcc hx
        simpa [Set.uIcc] using this
      have hmem : (Y, x) ∈ Set.Icc (Y₀ - 1) (Y₀ + 1) ×ˢ Set.Icc (min x₁ x₂) (max x₁ x₂) :=
        ⟨⟨le_of_lt hY.1, le_of_lt hY.2⟩, hxle⟩
      have := hC (Y, x) hmem
      simpa [Function.uncurry] using this
    · exact intervalIntegrable_const
    · filter_upwards with x hx
      rw [Set.mem_uIoc] at hx
      have hxab : a < x ∧ x < b := by
        rcases hx with ⟨hx1, hx2⟩ | ⟨hx2, hx1⟩
        · exact ⟨by linarith [h₁.1, hx1], by linarith [h₂.2, hx2]⟩
        · exact ⟨by linarith [h₂.1, hx2], by linarith [h₁.2, hx1]⟩
      have hxstrip : ((x : ℂ) + (Y₀ : ℂ) * Complex.I) ∈ {z : ℂ | a < z.re ∧ z.re < b} := by
        simp only [Set.mem_ofPred_eq]
        have hre : ((x : ℂ) + (Y₀ : ℂ) * Complex.I).re = x := by simp
        rw [hre]
        exact hxab
      have hd0 : DifferentiableAt ℂ h ((x : ℂ) + (Y₀ : ℂ) * Complex.I) :=
        hhol.differentiableAt (hopen.mem_nhds hxstrip)
      have hm : ContinuousAt (fun Y : ℝ => ((x : ℂ) + (Y : ℂ) * Complex.I)) Y₀ :=
        (by fun_prop : Continuous fun Y : ℝ => ((x : ℂ) + (Y : ℂ) * Complex.I)).continuousAt
      exact (hd0.continuousAt.comp
        (f := fun Y : ℝ => ((x : ℂ) + (Y : ℂ) * Complex.I)) hm).norm
  refine ⟨hcont, ?_⟩
  -- ## The Fubini bound
  intro Y₁ Y₂ hY
  set φ : ℝ → ℝ := fun Y => ∫ x : ℝ in x₁..x₂, ‖h ((x : ℂ) + Y * Complex.I)‖ with hφdef
  have hφnn : ∀ Y, 0 ≤ φ Y :=
    fun Y => intervalIntegral.integral_nonneg hx12 (fun x _ => norm_nonneg _)
  have hφmeas : AEStronglyMeasurable φ (volume.restrict (Set.Ioc Y₁ Y₂)) :=
    hcont.aestronglyMeasurable
  have houter : ∫ Y : ℝ in Y₁..Y₂, φ Y
      = (∫⁻ Y in Set.Ioc Y₁ Y₂, ENNReal.ofReal (φ Y)).toReal := by
    rw [intervalIntegral.integral_of_le hY]
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hφnn) hφmeas
  rw [houter]
  -- measurability of the uncurried integrand, for Tonelli
  have hAE : AEMeasurable
      (Function.uncurry (fun (Y x : ℝ) => ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖))
      ((volume.restrict (Set.Ioc Y₁ Y₂)).prod (volume.restrict (Set.Ioc x₁ x₂))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    have hstrip : ContinuousOn h {z : ℂ | a < z.re ∧ z.re < b} := hhol.continuousOn
    have hmaps : MapsTo (fun q : ℝ × ℝ => ((q.2 : ℂ) + q.1 * Complex.I))
        (Set.Ioc Y₁ Y₂ ×ˢ Set.Ioc x₁ x₂) {z : ℂ | a < z.re ∧ z.re < b} := by
      intro q hq
      simp only [Set.mem_prod, Set.mem_Ioc] at hq
      simp only [Set.mem_ofPred_eq]
      have hre : ((q.2 : ℂ) + q.1 * Complex.I).re = q.2 := by simp
      rw [hre]
      exact ⟨by linarith [h₁.1, hq.2.1], by linarith [h₂.2, hq.2.2]⟩
    have hc : ContinuousOn (fun q : ℝ × ℝ => h ((q.2 : ℂ) + q.1 * Complex.I))
        (Set.Ioc Y₁ Y₂ ×ˢ Set.Ioc x₁ x₂) := hstrip.comp (by fun_prop) hmaps
    exact ContinuousOn.aemeasurable
      (ENNReal.continuous_ofReal.comp_continuousOn hc.norm)
      (measurableSet_Ioc.prod measurableSet_Ioc)
  -- pointwise bound of the outer integrand
  have hpt : ∀ Y : ℝ, ENNReal.ofReal (φ Y)
      ≤ ∫⁻ x in Set.Ioc x₁ x₂, ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖ := by
    intro Y
    have hc : ContinuousOn (fun x : ℝ => h ((x : ℂ) + Y * Complex.I)) (Set.Ioc x₁ x₂) := by
      have hstrip : ContinuousOn h {z : ℂ | a < z.re ∧ z.re < b} := hhol.continuousOn
      have hmaps : MapsTo (fun x : ℝ => ((x : ℂ) + Y * Complex.I)) (Set.Ioc x₁ x₂)
          {z : ℂ | a < z.re ∧ z.re < b} := by
        intro x hx
        simp only [Set.mem_ofPred_eq, Set.mem_Ioc] at hx ⊢
        have hre : ((x : ℂ) + Y * Complex.I).re = x := by simp
        rw [hre]
        exact ⟨by linarith [h₁.1, hx.1], by linarith [h₂.2, hx.2]⟩
      exact hstrip.comp (by fun_prop) hmaps
    have hms : AEStronglyMeasurable (fun x : ℝ => ‖h ((x : ℂ) + Y * Complex.I)‖)
        (volume.restrict (Set.Ioc x₁ x₂)) := hc.norm.aestronglyMeasurable measurableSet_Ioc
    rw [hφdef]
    calc ENNReal.ofReal (∫ x : ℝ in x₁..x₂, ‖h ((x : ℂ) + Y * Complex.I)‖)
        = ENNReal.ofReal
            ((∫⁻ x in Set.Ioc x₁ x₂, ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖).toReal) := by
          rw [intervalIntegral.integral_of_le hx12,
            MeasureTheory.integral_eq_lintegral_of_nonneg_ae
              (Eventually.of_forall fun x => norm_nonneg _) hms]
      _ ≤ ∫⁻ x in Set.Ioc x₁ x₂, ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖ :=
          ENNReal.ofReal_toReal_le
  have hstep : ∫⁻ Y in Set.Ioc Y₁ Y₂, ENNReal.ofReal (φ Y)
      ≤ ∫⁻ Y in Set.Ioc Y₁ Y₂, ∫⁻ x in Set.Ioc x₁ x₂,
          ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖ :=
    lintegral_mono_ae (Eventually.of_forall hpt)
  have hswap : ∫⁻ Y in Set.Ioc Y₁ Y₂, (∫⁻ x in Set.Ioc x₁ x₂,
        ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖)
      = ∫⁻ x in Set.Ioc x₁ x₂, ∫⁻ Y in Set.Ioc Y₁ Y₂,
        ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖ :=
    MeasureTheory.lintegral_lintegral_swap
      (f := fun (Y x : ℝ) => ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖) hAE
  have hstep2 : ∫⁻ x in Set.Ioc x₁ x₂, (∫⁻ Y in Set.Ioc Y₁ Y₂,
        ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖)
      ≤ ∫⁻ x in Set.Ioc x₁ x₂, ENNReal.ofReal m := by
    apply lintegral_mono_ae
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have hx' : x ∈ Set.Ioo a b := ⟨by linarith [h₁.1, hx.1], by linarith [h₂.2, hx.2]⟩
    have h1 : ∫⁻ Y in Set.Ioc Y₁ Y₂, ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖
        ≤ ∫⁻ Y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + Y * Complex.I)‖ := by
      simpa using MeasureTheory.lintegral_mono_set (μ := volume) (s := Set.Ioc Y₁ Y₂)
        (t := Set.univ) (Set.subset_univ _)
    exact h1.trans (hmass x hx')
  have hstep3 : ∫⁻ x in Set.Ioc x₁ x₂, ENNReal.ofReal m
      = ENNReal.ofReal m * ENNReal.ofReal (x₂ - x₁) := by
    rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc]
  have hfin : ∫⁻ Y in Set.Ioc Y₁ Y₂, ENNReal.ofReal (φ Y)
      ≤ ENNReal.ofReal m * ENNReal.ofReal (x₂ - x₁) :=
    hstep.trans (hswap.le.trans (hstep2.trans hstep3.le))
  calc (∫⁻ Y in Set.Ioc Y₁ Y₂, ENNReal.ofReal (φ Y)).toReal
      ≤ (ENNReal.ofReal m * ENNReal.ofReal (x₂ - x₁)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hfin
    _ = (x₂ - x₁) * max m 0 := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal (sub_nonneg.mpr hx12)]
        ring

end Work.FatouL1
