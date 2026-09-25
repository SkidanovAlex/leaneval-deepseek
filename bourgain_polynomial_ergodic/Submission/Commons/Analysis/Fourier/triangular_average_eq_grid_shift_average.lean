import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Commons.Analysis.Fourier.grid_shift_kernel_eq_triangular

namespace Commons.Analysis.Fourier

open MeasureTheory

private lemma grid_floor_le_iff (k : ℤ) (x θ w : ℝ) :
    (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) ≤ w)
      ↔ ((⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) ≤ (w - θ) * (2:ℝ)^k) := by
  have hN : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) _
  have hNne : (2:ℝ)^k ≠ 0 := ne_of_gt hN
  have hLinv : (2:ℝ)^(-k) = ((2:ℝ)^k)⁻¹ := by rw [zpow_neg]
  rw [hLinv]
  constructor
  · intro h
    have h2 : (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * ((2:ℝ)^k)⁻¹ ≤ w - θ := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hN.le
    rwa [mul_assoc, inv_mul_cancel₀ hNne, mul_one] at h3
  · intro h
    have h3 := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hN.le)
    have h4 : (w - θ) * (2:ℝ)^k * ((2:ℝ)^k)⁻¹ = w - θ := by
      rw [mul_assoc, mul_inv_cancel₀ hNne, mul_one]
    rw [h4] at h3
    linarith

private lemma grid_floor_lt_iff (k : ℤ) (x θ w : ℝ) :
    (w < θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k))
      ↔ ((w - θ) * (2:ℝ)^k < (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) + 1) := by
  have hN : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) _
  have hNne : (2:ℝ)^k ≠ 0 := ne_of_gt hN
  have hLinv : (2:ℝ)^(-k) = ((2:ℝ)^k)⁻¹ := by rw [zpow_neg]
  rw [hLinv]
  constructor
  · intro h
    have h5 : (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * ((2:ℝ)^k)⁻¹ + ((2:ℝ)^k)⁻¹
        = ((⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) + 1) * ((2:ℝ)^k)⁻¹ := by ring
    have h3 : (w - θ) < ((⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) + 1) * ((2:ℝ)^k)⁻¹ := by linarith
    have h4 := mul_lt_mul_of_pos_right h3 hN
    rwa [mul_assoc, inv_mul_cancel₀ hNne, mul_one] at h4
  · intro h
    have h3 := mul_lt_mul_of_pos_right h (inv_pos.mpr hN)
    have h4 : (w - θ) * (2:ℝ)^k * ((2:ℝ)^k)⁻¹ = w - θ := by
      rw [mul_assoc, mul_inv_cancel₀ hNne, mul_one]
    rw [h4] at h3
    have h5 : ((⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) + 1) * ((2:ℝ)^k)⁻¹
        = (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * ((2:ℝ)^k)⁻¹ + ((2:ℝ)^k)⁻¹ := by ring
    linarith

/-- The set of `y` with `⌊(y-θ)·2^k⌋ = ⌊(x-θ)·2^k⌋` is exactly the half-open grid cell
`[θ + ⌊(x-θ)·2^k⌋·2^{-k}, θ + ⌊(x-θ)·2^k⌋·2^{-k} + 2^{-k})`. -/
private lemma grid_floor_set_eq_Ico (k : ℤ) (x θ : ℝ) :
    {y : ℝ | ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋}
      = Set.Ico (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
                (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)) := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  rw [Int.floor_eq_iff, grid_floor_le_iff k x θ y, grid_floor_lt_iff k x θ y]

/-- The Lebesgue integral of `g` over the grid cell equals the integral of `g` times the
`{0,1}`-kernel selecting the cell containing `x`. -/
private lemma setIntegral_gridCell_eq_kernel (k : ℤ) (x θ : ℝ) (g : ℝ → ℂ) :
    (∫ y in Set.Ioc (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
          (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y)
      = ∫ y, g y * (((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ) := by
  have hset := grid_floor_set_eq_Ico k x θ
  have hIocIco : Set.Ioc (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
        (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k))
      =ᵐ[volume] Set.Ico (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
        (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)) :=
    (Ico_ae_eq_Ioc (μ := volume)).symm
  rw [setIntegral_congr_set hIocIco, ← integral_indicator measurableSet_Ico]
  apply integral_congr_ae
  filter_upwards with y
  rw [Set.indicator_apply]
  have hmem : y ∈ Set.Ico (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
        (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k))
      ↔ ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ := by
    rw [← hset]; exact Iff.rfl
  by_cases h : y ∈ Set.Ico (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
        (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k))
  · rw [if_pos h, if_pos (hmem.mp h)]; simp
  · rw [if_neg h, if_neg (fun hc => h (hmem.mpr hc))]; simp

/-- Extracting a real scalar factor written as a product from a `ℂ`-valued integral. -/
private lemma integral_mul_ofReal_factor (g : ℝ → ℂ) (a : ℝ) (f : ℝ → ℝ) :
    (∫ y, g y * ((a * f y : ℝ) : ℂ)) = (a : ℂ) * ∫ y, g y * ((f y : ℝ) : ℂ) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [Complex.ofReal_mul]
  ring

theorem triangular_average_eq_grid_shift_average
    (K k : ℤ) (hKk : K ≤ k) (g : ℝ → ℂ) (hg : MeasureTheory.Integrable g MeasureTheory.volume)
    (x : ℝ) :
    (∫ y : ℝ, g y * ((2:ℝ)^k * max 0 (1 - (2:ℝ)^k * |x - y|)))
      = (1 / (2:ℝ)^(-K)) * ∫ θ in (0:ℝ)..((2:ℝ)^(-K)),
          ((2:ℝ)^k * ∫ y in Set.Ioc (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
              (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y) := by
  have hMpos : (0:ℝ) < (2:ℝ)^(-K) := zpow_pos (by norm_num) _
  have hMne : (2:ℝ)^(-K) ≠ 0 := ne_of_gt hMpos
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) ((2:ℝ)^(-K)))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Set.uIoc_of_le hMpos.le, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hKmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (((if ⌊(p.2 - p.1) * (2:ℝ)^k⌋ = ⌊(x - p.1) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ))
      ((volume.restrict (Set.uIoc (0:ℝ) ((2:ℝ)^(-K)))).prod volume) := by
    have h1 : Measurable (fun p : ℝ × ℝ => ⌊(p.2 - p.1) * (2:ℝ)^k⌋) := by fun_prop
    have h2 : Measurable (fun p : ℝ × ℝ => ⌊(x - p.1) * (2:ℝ)^k⌋) := by fun_prop
    exact (Complex.continuous_ofReal.measurable.comp
      (Measurable.ite (measurableSet_eq_fun h1 h2) measurable_const measurable_const)).aestronglyMeasurable
  have hIntK : Integrable
      (Function.uncurry (fun θ y => g y * (((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ)))
      ((volume.restrict (Set.uIoc (0:ℝ) ((2:ℝ)^(-K)))).prod volume) := by
    have hgnorm : Integrable (fun p : ℝ × ℝ => ‖g p.2‖)
        ((volume.restrict (Set.uIoc (0:ℝ) ((2:ℝ)^(-K)))).prod volume) :=
      hg.norm.comp_snd _
    refine hgnorm.mono' ?_ ?_
    · change AEStronglyMeasurable
        (fun p : ℝ × ℝ => g p.2 * (((if ⌊(p.2 - p.1) * (2:ℝ)^k⌋ = ⌊(x - p.1) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ))
        ((volume.restrict (Set.uIoc (0:ℝ) ((2:ℝ)^(-K)))).prod volume)
      exact (hg.comp_snd (volume.restrict (Set.uIoc (0:ℝ) ((2:ℝ)^(-K))))).aestronglyMeasurable.mul hKmeas
    · filter_upwards with p
      change ‖g p.2 * (((if ⌊(p.2 - p.1) * (2:ℝ)^k⌋ = ⌊(x - p.1) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ)‖ ≤ ‖g p.2‖
      by_cases h : ⌊(p.2 - p.1) * (2:ℝ)^k⌋ = ⌊(x - p.1) * (2:ℝ)^k⌋
      · rw [if_pos h]; simp
      · rw [if_neg h]; simp
  have hgrid : ∀ y : ℝ,
      (∫ θ in (0:ℝ)..((2:ℝ)^(-K)), (if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0))
        = (2:ℝ)^(-K) * max 0 (1 - (2:ℝ)^k * |x - y|) := by
    intro y
    have h := grid_shift_kernel_eq_triangular K k hKk x y
    rw [← h, one_div, ← mul_assoc, mul_inv_cancel₀ hMne, one_mul]
  have he1 : (∫ θ in (0:ℝ)..((2:ℝ)^(-K)),
        ((2:ℝ)^k * ∫ y in Set.Ioc (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
              (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y))
      = (∫ θ in (0:ℝ)..((2:ℝ)^(-K)), ((2:ℝ)^k * ∫ y, g y *
              (((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro θ _
    beta_reduce
    rw [setIntegral_gridCell_eq_kernel k x θ g]
  have he2 : (∫ θ in (0:ℝ)..((2:ℝ)^(-K)), ((2:ℝ)^k * ∫ y, g y *
              (((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ)))
      = (2:ℝ)^k * (∫ θ in (0:ℝ)..((2:ℝ)^(-K)), ∫ y, g y *
              (((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_const_mul]
  have he3 : (∫ θ in (0:ℝ)..((2:ℝ)^(-K)), ∫ y, g y *
              (((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ))
      = ∫ y, ∫ θ in (0:ℝ)..((2:ℝ)^(-K)), g y *
              (((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ) :=
    intervalIntegral_integral_swap hIntK
  have he4 : (∫ y, ∫ θ in (0:ℝ)..((2:ℝ)^(-K)), g y *
              (((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ))
      = ∫ y, g y * (∫ θ in (0:ℝ)..((2:ℝ)^(-K)),
              (((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ)) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [intervalIntegral.integral_const_mul]
  have he5 : (∫ y, g y * (∫ θ in (0:ℝ)..((2:ℝ)^(-K)),
              (((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ) : ℂ)))
      = ∫ y, g y * (((∫ θ in (0:ℝ)..((2:ℝ)^(-K)),
              ((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ)) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [intervalIntegral.integral_ofReal]
  have he6 : (∫ y, g y * (((∫ θ in (0:ℝ)..((2:ℝ)^(-K)),
              ((if ⌊(y - θ) * (2:ℝ)^k⌋ = ⌊(x - θ) * (2:ℝ)^k⌋ then (1:ℝ) else 0) : ℝ)) : ℝ) : ℂ))
      = ∫ y, g y * ((((2:ℝ)^(-K)) * max 0 (1 - (2:ℝ)^k * |x - y|) : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [hgrid y]
  have he7 : (∫ y, g y * ((((2:ℝ)^(-K)) * max 0 (1 - (2:ℝ)^k * |x - y|) : ℝ) : ℂ))
      = (((2:ℝ)^(-K) : ℝ) : ℂ) * ∫ y, g y * ((max 0 (1 - (2:ℝ)^k * |x - y|) : ℝ) : ℂ) :=
    integral_mul_ofReal_factor g ((2:ℝ)^(-K)) (fun y => max 0 (1 - (2:ℝ)^k * |x - y|))
  have hInner := he1.trans (he2.trans (congrArg (fun W : ℂ => (2:ℝ)^k * W)
      (he3.trans (he4.trans (he5.trans (he6.trans he7))))))
  have hscalar : (1 / (2:ℝ)^(-K)) * ((2:ℝ)^k * ((((2:ℝ)^(-K) : ℝ) : ℂ) *
        (∫ y, g y * ((max 0 (1 - (2:ℝ)^k * |x - y|) : ℝ) : ℂ)))) =
      (2:ℝ)^k * (∫ y, g y * ((max 0 (1 - (2:ℝ)^k * |x - y|) : ℝ) : ℂ)) := by
    have hM1 : (1 / (2:ℝ)^(-K)) * ((((2:ℝ)^(-K) : ℝ) : ℂ)) = 1 := by
      rw [one_div, Complex.ofReal_zpow (2:ℝ) (-K)]
      exact inv_mul_cancel₀ (zpow_ne_zero (-K) (by norm_num))
    rw [show (2:ℝ)^k * ((((2:ℝ)^(-K) : ℝ) : ℂ) *
          (∫ y, g y * ((max 0 (1 - (2:ℝ)^k * |x - y|) : ℝ) : ℂ)))
        = ((((2:ℝ)^(-K) : ℝ) : ℂ)) * ((2:ℝ)^k *
          (∫ y, g y * ((max 0 (1 - (2:ℝ)^k * |x - y|) : ℝ) : ℂ))) from by ring]
    rw [← mul_assoc, hM1, one_mul]
  have hLHS : (2:ℝ)^k * (∫ y, g y * ((max 0 (1 - (2:ℝ)^k * |x - y|) : ℝ) : ℂ))
      = ∫ y : ℝ, g y * ((2:ℝ)^k * max 0 (1 - (2:ℝ)^k * |x - y|)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring
  have hRHS : (1 / (2:ℝ)^(-K)) * (∫ θ in (0:ℝ)..((2:ℝ)^(-K)),
          ((2:ℝ)^k * ∫ y in Set.Ioc (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
              (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y))
      = ∫ y : ℝ, g y * ((2:ℝ)^k * max 0 (1 - (2:ℝ)^k * |x - y|)) := by
    rw [hInner, hscalar, hLHS]
  exact hRHS.symm

end Commons.Analysis.Fourier