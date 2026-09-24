import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Commons.Analysis.Fourier.fourier_ofReal_eq_two_mul_integral_Ici_cos

noncomputable section
open MeasureTheory Real
open scoped FourierTransform Real

namespace Commons.Analysis.Fourier

/-! ### General even Fourier lemma -/

theorem fourier_ofReal_of_even {g : ℝ → ℝ} (hg : Integrable g) (heven : Function.Even g) (ξ : ℝ) :
    𝓕 (fun t : ℝ => (g t : ℂ)) ξ
      = ((∫ t : ℝ, g t * Real.cos (2 * Real.pi * ξ * t) : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun v => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * (g v : ℂ)
    with hF_def
  have hFmeas : AEStronglyMeasurable F := by rw [hF_def]; fun_prop
  have hFint : Integrable F := by
    refine Integrable.mono' hg.norm hFmeas ?_
    filter_upwards with v
    rw [hF_def]
    simp only [Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    simp [Real.norm_eq_abs]
  have hfour : 𝓕 (fun t : ℝ => (g t : ℂ)) ξ = ∫ v, F v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, hF_def]
  have hre : (∫ v, F v).re = ∫ v, (F v).re := (integral_re hFint).symm
  have him : (∫ v, F v).im = ∫ v, (F v).im := (integral_im hFint).symm
  have hre_pt : ∀ v, (F v).re = g v * Real.cos (2 * Real.pi * ξ * v) := by
    intro v
    rw [hF_def]
    simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [show (-2 * Real.pi * v * ξ) = -(2 * Real.pi * ξ * v) by ring, Real.cos_neg]
    ring
  have him_pt : ∀ v, (F v).im = Real.sin (-2 * Real.pi * v * ξ) * g v := by
    intro v
    rw [hF_def]
    simp only [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  have hreval : (∫ v, F v).re = ∫ v, g v * Real.cos (2 * Real.pi * ξ * v) := by
    rw [hre]
    exact integral_congr_ae (Filter.Eventually.of_forall hre_pt)
  have him_zero : (∫ v, F v).im = 0 := by
    rw [him]
    rw [show (∫ v, (F v).im) = ∫ v, Real.sin (-2 * Real.pi * v * ξ) * g v from
      integral_congr_ae (Filter.Eventually.of_forall him_pt)]
    apply integral_eq_zero_of_odd
    intro v
    show Real.sin (-2 * Real.pi * (-v) * ξ) * g (-v)
      = -(Real.sin (-2 * Real.pi * v * ξ) * g v)
    rw [heven v]
    rw [show (-2 * Real.pi * (-v) * ξ) = -(-2 * Real.pi * v * ξ) by ring, Real.sin_neg]
    ring
  rw [hfour]
  have hself : (∫ v, F v) = (((∫ v, F v).re) : ℂ) := by
    apply Complex.ext <;> simp [him_zero]
  rw [hself, hreval]

/-! ### Integrability and parity of the Fejer kernel `sinc (π y)^2` -/

lemma abs_sinc_le_inv_abs {u : ℝ} (hu : u ≠ 0) : |Real.sinc u| ≤ |u|⁻¹ := by
  rw [Real.sinc_of_ne_zero hu, abs_div]
  simpa using div_le_div_of_nonneg_right (abs_sin_le_one u) (abs_nonneg u)

lemma sinc_sq_le_two_div_one_add_sq (u : ℝ) : Real.sinc u ^ 2 ≤ 2 / (1 + u ^ 2) := by
  rcases le_or_gt 1 |u| with h | h
  · have hu : u ≠ 0 := by intro h0; rw [h0, abs_zero] at h; linarith
    have h2 : |Real.sinc u| ≤ |u|⁻¹ := abs_sinc_le_inv_abs hu
    have h3 : Real.sinc u ^ 2 ≤ (|u|⁻¹)^2 := by
      rw [← sq_abs (Real.sinc u)]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    have h4 : (|u|⁻¹)^2 = 1/u^2 := by rw [inv_pow, sq_abs, one_div]
    have h5 : (1:ℝ) ≤ u^2 := by
      have := sq_abs u
      nlinarith [h, abs_nonneg u]
    have h6 : (1:ℝ)/u^2 ≤ 2/(1+u^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc Real.sinc u ^ 2 ≤ (|u|⁻¹)^2 := h3
      _ = 1/u^2 := h4
      _ ≤ 2/(1+u^2) := h6
  · have h1 : Real.sinc u ^ 2 ≤ 1 := by
      have := abs_sinc_le_one u
      rw [← sq_abs (Real.sinc u)]
      nlinarith [this, abs_nonneg (Real.sinc u)]
    have h2 : (1:ℝ) ≤ 2/(1+u^2) := by
      rw [le_div_iff₀ (by positivity)]
      have h3 : u^2 ≤ 1 := by
        have := sq_abs u
        nlinarith [h, abs_nonneg u]
      linarith
    linarith

lemma integrable_sinc_pi_sq : Integrable (fun y : ℝ => Real.sinc (Real.pi * y) ^ 2) := by
  have hbase : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
  have hcomp := hbase.comp_mul_right' Real.pi_ne_zero
  have hg : Integrable (fun y : ℝ => 2 / (1 + (Real.pi * y) ^ 2)) := by
    have h' : (fun y : ℝ => 2 / (1 + (Real.pi*y)^2))
        = fun y : ℝ => 2 * ((fun x : ℝ => (1+x^2)⁻¹) (y * Real.pi)) := by
      funext y; rw [div_eq_mul_inv, mul_comm y Real.pi]
    rw [h']
    exact hcomp.const_mul 2
  refine Integrable.mono' hg ?_ ?_
  · exact (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2 |>.aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sinc_sq_le_two_div_one_add_sq (Real.pi * y)

lemma even_sinc_pi_sq : Function.Even (fun y : ℝ => Real.sinc (Real.pi * y) ^ 2) := by
  intro y
  show Real.sinc (Real.pi * (-y)) ^ 2 = Real.sinc (Real.pi * y) ^ 2
  rw [mul_neg, Real.sinc_neg]

/-! ### The triangle (tent) function -/

/-- The triangle function `x ↦ max (1 - |x|) 0`. -/
noncomputable def tri (x : ℝ) : ℝ := max (1 - |x|) 0

lemma tri_continuous : Continuous tri := by
  unfold tri; fun_prop

lemma tri_even : Function.Even tri := by
  intro x
  show max (1 - |(-x)|) 0 = max (1 - |x|) 0
  rw [abs_neg]

lemma tri_eq_zero_of_one_le_abs {x : ℝ} (h : 1 ≤ |x|) : tri x = 0 := by
  show max (1 - |x|) 0 = 0
  rw [max_eq_right]
  linarith

lemma tri_eq_one_sub {x : ℝ} (h : |x| ≤ 1) : tri x = 1 - |x| := by
  show max (1 - |x|) 0 = 1 - |x|
  rw [max_eq_left]
  linarith

lemma tri_integrable : Integrable tri := by
  refine Continuous.integrable_of_hasCompactSupport tri_continuous ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1:ℝ)) (b := 1)) ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hmem
  refine hx (tri_eq_zero_of_one_le_abs ?_)
  by_contra hc
  rw [not_le] at hc
  exact hmem (by rw [Set.mem_Icc, ← abs_le]; exact hc.le)

/-! ### The computation `∫ tri · cos = sinc²` -/

lemma integral_tri_mul_eq (ξ : ℝ) :
    ∫ t : ℝ, tri t * Real.cos (2 * Real.pi * ξ * t)
      = 2 * ∫ t in (0:ℝ)..1, (1 - t) * Real.cos (2 * Real.pi * ξ * t) := by
  have hpt : ∀ t, tri t * Real.cos (2 * Real.pi * ξ * t)
      = (Set.Icc (-1:ℝ) 1).indicator
          (fun t => (1 - |t|) * Real.cos (2 * Real.pi * ξ * t)) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (-1:ℝ) 1
    · rw [Set.indicator_of_mem ht]
      rw [tri_eq_one_sub (by rw [abs_le]; exact ht)]
    · rw [Set.indicator_of_notMem ht]
      have h1 : 1 ≤ |t| := by
        by_contra hc
        rw [not_le] at hc
        exact ht (by rw [Set.mem_Icc, ← abs_le]; exact hc.le)
      rw [tri_eq_zero_of_one_le_abs h1, zero_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1:ℝ) ≤ 1 by norm_num)]
  have hcont : Continuous (fun t : ℝ => (1 - |t|) * Real.cos (2 * Real.pi * ξ * t)) := by fun_prop
  have hA : IntervalIntegrable (fun t : ℝ => (1 - |t|) * Real.cos (2 * Real.pi * ξ * t)) volume (-1) 0 :=
    hcont.intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t : ℝ => (1 - |t|) * Real.cos (2 * Real.pi * ξ * t)) volume 0 1 :=
    hcont.intervalIntegrable _ _
  rw [(intervalIntegral.integral_add_adjacent_intervals hA hB).symm]
  have h4 : ∫ t in (-1:ℝ)..0, (1 - |t|) * Real.cos (2 * Real.pi * ξ * t)
      = ∫ t in (0:ℝ)..1, (1 - |t|) * Real.cos (2 * Real.pi * ξ * t) := by
    rw [show ∫ t in (-1:ℝ)..0, (1 - |t|) * Real.cos (2 * Real.pi * ξ * t)
        = ∫ t in (-1:ℝ)..0, (1 - |(-t)|) * Real.cos (2 * Real.pi * ξ * (-t)) from by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only
      rw [abs_neg]
      congr 1
      rw [show 2 * Real.pi * ξ * (-x) = -(2 * Real.pi * ξ * x) by ring, Real.cos_neg]]
    simpa using intervalIntegral.integral_comp_neg
      (fun t : ℝ => (1 - |t|) * Real.cos (2 * Real.pi * ξ * t)) (a := (-1:ℝ)) (b := 0)
  have h5 : ∫ t in (0:ℝ)..1, (1 - |t|) * Real.cos (2 * Real.pi * ξ * t)
      = ∫ t in (0:ℝ)..1, (1 - t) * Real.cos (2 * Real.pi * ξ * t) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := by
      have : x ∈ Set.Icc (0:ℝ) 1 := by rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      exact this.1
    simp only []
    rw [abs_of_nonneg hx0]
  rw [h4, h5]
  ring

lemma hasDerivAt_antideriv (a : ℝ) (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (1 - x) * Real.sin (a * x) / a - Real.cos (a * x) / a ^ 2)
      ((1 - t) * Real.cos (a * t)) t := by
  have hpath : HasDerivAt (fun x : ℝ => a * x) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have hs := (Real.hasDerivAt_sin (a*t)).comp t hpath
  have hc := (Real.hasDerivAt_cos (a*t)).comp t hpath
  have h1 := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul hs).div_const a
  have h2 := hc.div_const (a^2)
  have hh := h1.sub h2
  have hgoal : (((0 - 1) * Real.sin (a*t) + (1 - t) * (Real.cos (a*t) * a)) / a
        - -Real.sin (a*t) * a / a^2) = (1-t)*Real.cos (a*t) := by
    field_simp
    ring
  rw [← hgoal]
  exact hh

lemma integral_one_sub_mul_cos (a : ℝ) (ha : a ≠ 0) :
    ∫ t in (0:ℝ)..1, (1 - t) * Real.cos (a * t) = (1 - Real.cos a) / a ^ 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => (1 - x) * Real.sin (a * x) / a - Real.cos (a * x) / a ^ 2)
        ((1 - t) * Real.cos (a * t)) t := fun t _ => hasDerivAt_antideriv a ha t
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t) * Real.cos (a * t)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => (1 - t) * Real.cos (a * t)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_one, sub_self, mul_zero, zero_mul, zero_div, Real.sin_zero, Real.cos_zero,
    sub_zero]
  field_simp
  ring

lemma integral_tri_cos (ξ : ℝ) :
    ∫ t : ℝ, tri t * Real.cos (2 * Real.pi * ξ * t) = Real.sinc (Real.pi * ξ) ^ 2 := by
  rw [integral_tri_mul_eq ξ]
  rcases eq_or_ne ξ 0 with hξ | hξ
  · subst hξ
    have h : (∫ t in (0:ℝ)..1, (1 - t) * Real.cos (2 * Real.pi * 0 * t)) = 1/2 := by
      simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun x : ℝ => x)
        (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
      rw [intervalIntegral.integral_const, integral_id]
      norm_num
    rw [h]
    simp only [mul_zero, Real.sinc_zero]
    norm_num
  · have ha : (2 * Real.pi * ξ) ≠ 0 := by
      have h2 : (2:ℝ) * Real.pi ≠ 0 := by positivity
      exact mul_ne_zero h2 hξ
    rw [integral_one_sub_mul_cos (2 * Real.pi * ξ) ha]
    have hπξ : Real.pi * ξ ≠ 0 := mul_ne_zero Real.pi_ne_zero hξ
    rw [Real.sinc_of_ne_zero hπξ]
    have htrig : Real.cos (2 * Real.pi * ξ) = 1 - 2 * Real.sin (Real.pi * ξ) ^ 2 := by
      rw [show 2 * Real.pi * ξ = 2 * (Real.pi * ξ) by ring, Real.cos_two_mul]
      have := Real.sin_sq (Real.pi * ξ)
      linarith
    rw [htrig]
    have hsq : (2 * Real.pi * ξ) ^ 2 = 4 * (Real.pi * ξ) ^ 2 := by ring
    rw [hsq]
    field_simp
    ring

/-! ### The target theorem -/

theorem triangle_kernel_fourier_inversion :
    ∀ ξ : ℝ, ∫ y : ℝ, (if y = 0 then 1 else (Real.sin (Real.pi * y) / (Real.pi * y)) ^ 2) * Real.cos (2 * Real.pi * ξ * y)
      = max (1 - |ξ|) 0 := by
  intro ξ
  have hpt : ∀ y, (if y = 0 then 1 else (Real.sin (Real.pi * y) / (Real.pi * y)) ^ 2)
      = Real.sinc (Real.pi * y) ^ 2 := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [Real.sinc_zero]
    · rw [if_neg hy, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hy)]
  rw [show (∫ y : ℝ, (if y = 0 then 1 else (Real.sin (Real.pi * y) / (Real.pi * y)) ^ 2)
        * Real.cos (2 * Real.pi * ξ * y))
      = ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Real.cos (2 * Real.pi * ξ * y) from
    integral_congr_ae (Filter.Eventually.of_forall (fun y => by simp only [hpt]))]
  have htri_int : Integrable tri := tri_integrable
  have htri_cont : Continuous tri := tri_continuous
  have htri_even : Function.Even tri := tri_even
  set G : ℝ → ℂ := fun w => ((Real.sinc (Real.pi * w) ^ 2 : ℝ) : ℂ) with hG_def
  have hFtri : 𝓕 (fun t : ℝ => (tri t : ℂ)) = G := by
    funext w
    rw [hG_def]
    rw [fourier_ofReal_of_even htri_int htri_even w, integral_tri_cos w]
  have hFtri_int : Integrable (𝓕 (fun t : ℝ => (tri t : ℂ))) := by
    rw [hFtri]; exact integrable_sinc_pi_sq.ofReal
  have hinv : 𝓕⁻ G = fun t : ℝ => (tri t : ℂ) := by
    have hcont : Continuous (fun t : ℝ => (tri t : ℂ)) := Complex.continuous_ofReal.comp htri_cont
    have := Continuous.fourierInv_fourier_eq (f := fun t : ℝ => (tri t : ℂ)) hcont htri_int.ofReal hFtri_int
    rwa [hFtri] at this
  have hcos : (∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 * Real.cos (2 * Real.pi * (-ξ) * t))
      = ∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 * Real.cos (2 * Real.pi * ξ * t) := by
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    rw [show 2 * Real.pi * (-ξ) * t = -(2 * Real.pi * ξ * t) by ring, Real.cos_neg]
  have hmain : ((∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 * Real.cos (2 * Real.pi * ξ * t) : ℝ) : ℂ)
      = (tri ξ : ℂ) := by
    have h1 : (𝓕⁻ G) ξ = (tri ξ : ℂ) := by rw [hinv]
    rw [fourierInv_eq_fourier_neg] at h1
    have h2 : 𝓕 G (-ξ)
        = ((∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 * Real.cos (2 * Real.pi * (-ξ) * t) : ℝ) : ℂ) := by
      rw [hG_def]
      simpa using fourier_ofReal_of_even integrable_sinc_pi_sq even_sinc_pi_sq (-ξ)
    rw [h2, hcos] at h1
    exact h1
  have hreal : (∫ t : ℝ, Real.sinc (Real.pi * t) ^ 2 * Real.cos (2 * Real.pi * ξ * t)) = tri ξ :=
    Complex.ofReal_inj.mp hmain
  rw [hreal]
  rfl

end Commons.Analysis.Fourier
