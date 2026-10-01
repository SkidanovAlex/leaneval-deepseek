import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

/-!
# Laplace-transform estimate `laplace_F0_bound`

Bound for `∫₀^{x₀} e^{-zt} f(t) dt - f(0)/z` for a complex `z` with `Re z > 0`,
a function `f` with `f x₀ = 0`, and a bound `|f''| ≤ B` on `[0, x₀]`.
-/

namespace Commons.Analysis.Integral

open MeasureTheory intervalIntegral Filter
open scoped Topology

noncomputable def laplaceφ (z : ℂ) : ℝ → ℂ := fun t => Complex.exp ((-z) * (t : ℂ))

lemma laplaceφ_apply (z : ℂ) (t : ℝ) : laplaceφ z t = Complex.exp (-(z * (t : ℂ))) := by
  rw [laplaceφ, neg_mul]

lemma laplaceφ_zero (z : ℂ) : laplaceφ z 0 = 1 := by simp [laplaceφ]

lemma laplaceφ_hasDerivAt_raw (z : ℂ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp ((-z) * (y : ℂ)))
      ((-z) * Complex.exp ((-z) * (t : ℂ))) t := by
  have hlin : HasDerivAt (fun t : ℝ => (-z) * (t : ℂ)) (-z) t := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    simpa using h1.const_mul (-z)
  have h2 := (Complex.hasDerivAt_exp ((-z) * (t : ℂ))).comp t hlin
  simpa [Function.comp_def, mul_comm] using h2

lemma laplaceφ_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (laplaceφ z) ((-z) * laplaceφ z t) t :=
  laplaceφ_hasDerivAt_raw z t

lemma laplaceφ_norm_le (z : ℂ) (hz : 0 ≤ z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖laplaceφ z t‖ ≤ 1 := by
  rw [laplaceφ, Complex.norm_exp]
  have hre : ((-z) * (t : ℂ)).re = -(z.re * t) := by
    simp [Complex.mul_re, Complex.neg_re]
  rw [hre, Real.exp_le_one_iff]
  nlinarith

lemma laplaceφ_norm_sub_one_le (z : ℂ) (hz : 0 ≤ z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖laplaceφ z t - 1‖ ≤ ‖z‖ * t := by
  have hcont : ∀ s ∈ Set.Icc (0:ℝ) t,
      HasDerivWithinAt (laplaceφ z) ((-z) * laplaceφ z s) (Set.Icc 0 t) s :=
    fun s _ => (laplaceφ_hasDerivAt z s).hasDerivWithinAt
  have hbound : ∀ s ∈ Set.Icc (0:ℝ) t, ‖(-z) * laplaceφ z s‖ ≤ ‖z‖ := by
    intro s hs
    rw [norm_mul, norm_neg]
    calc ‖z‖ * ‖laplaceφ z s‖ ≤ ‖z‖ * 1 := by gcongr; exact laplaceφ_norm_le z hz hs.1
      _ = ‖z‖ := by ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hcont hbound (convex_Icc 0 t)
    (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht)
  rw [laplaceφ_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht] at h
  exact h

lemma continuous_laplaceφ (z : ℂ) : Continuous (laplaceφ z) := by
  have h : Continuous fun t : ℝ => (-z) * (t : ℂ) := continuous_const.mul Complex.continuous_ofReal
  exact Complex.continuous_exp.comp h

noncomputable def laplaceK (z : ℂ) (x₀ : ℝ) : ℝ → ℂ :=
  fun t => (laplaceφ z t - 1) / z ^ 2
    + (t : ℂ) * ((1 - laplaceφ z x₀) / ((x₀ : ℂ) * z ^ 2))

noncomputable def laplaceK' (z : ℂ) (x₀ : ℝ) : ℝ → ℂ :=
  fun t => -laplaceφ z t / z + (1 - laplaceφ z x₀) / ((x₀ : ℂ) * z ^ 2)

lemma continuous_laplaceK (z : ℂ) (x₀ : ℝ) : Continuous (laplaceK z x₀) := by
  have h1 : Continuous fun t : ℝ => (laplaceφ z t - 1) / z ^ 2 :=
    ((continuous_laplaceφ z).sub continuous_const).div_const _
  have h2 : Continuous fun t : ℝ => (t : ℂ) * ((1 - laplaceφ z x₀) / ((x₀ : ℂ) * z ^ 2)) :=
    Complex.continuous_ofReal.mul continuous_const
  exact h1.add h2

lemma continuous_laplaceK' (z : ℂ) (x₀ : ℝ) : Continuous (laplaceK' z x₀) := by
  have h1 : Continuous fun t : ℝ => -laplaceφ z t / z :=
    (continuous_laplaceφ z).neg.div_const _
  exact h1.add continuous_const

lemma laplaceK_zero (z : ℂ) (x₀ : ℝ) : laplaceK z x₀ 0 = 0 := by
  simp [laplaceK, laplaceφ]

lemma laplaceK_x0 (z : ℂ) (hz : z ≠ 0) (x₀ : ℝ) (hx₀ : x₀ ≠ 0) : laplaceK z x₀ x₀ = 0 := by
  have hx₀c : ((x₀ : ℂ)) ≠ 0 := by exact_mod_cast hx₀
  simp only [laplaceK]
  field_simp
  ring

lemma laplaceK_hasDerivAt (z : ℂ) (hz : z ≠ 0) (x₀ : ℝ) (t : ℝ) :
    HasDerivAt (laplaceK z x₀) (laplaceK' z x₀ t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (laplaceφ z s - 1) / z ^ 2)
      (((-z) * laplaceφ z t - 0) / z ^ 2) t :=
    ((laplaceφ_hasDerivAt z t).sub (hasDerivAt_const t 1)).div_const (z ^ 2)
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * ((1 - laplaceφ z x₀) / ((x₀ : ℂ) * z ^ 2)))
      (1 * ((1 - laplaceφ z x₀) / ((x₀ : ℂ) * z ^ 2))) t :=
    (hasDerivAt_id t).ofReal_comp.mul_const _
  have h := h1.add h2
  have hder : ((-z) * laplaceφ z t - 0) / z ^ 2
      + 1 * ((1 - laplaceφ z x₀) / ((x₀ : ℂ) * z ^ 2)) = laplaceK' z x₀ t := by
    rw [laplaceK', sub_zero, one_mul]
    field_simp
  rw [hder] at h
  exact h

lemma laplaceK'_hasDerivAt (z : ℂ) (hz : z ≠ 0) (x₀ : ℝ) (t : ℝ) :
    HasDerivAt (laplaceK' z x₀) (laplaceφ z t) t := by
  have h2 : HasDerivAt (fun s : ℝ => -laplaceφ z s / z) (-((-z) * laplaceφ z t) / z) t :=
    ((laplaceφ_hasDerivAt z t).neg).div_const z
  have h3 : HasDerivAt (fun _s : ℝ => (1 - laplaceφ z x₀) / ((x₀ : ℂ) * z ^ 2)) 0 t :=
    hasDerivAt_const t _
  have h := h2.add h3
  have hder : (-((-z) * laplaceφ z t) / z + 0) = laplaceφ z t := by
    field_simp
    ring
  rw [hder] at h
  exact h

lemma laplaceK'_zero (z : ℂ) (x₀ : ℝ) :
    laplaceK' z x₀ 0 = -1 / z + (1 - laplaceφ z x₀) / ((x₀ : ℂ) * z ^ 2) := by
  rw [laplaceK', laplaceφ_zero]

lemma laplaceK'_zero_key (z : ℂ) (hz : z ≠ 0) (x₀ : ℝ) (_hx₀ : x₀ ≠ 0) :
    -laplaceK' z x₀ 0 - 1 / z = (laplaceφ z x₀ - 1) / ((x₀ : ℂ) * z ^ 2) := by
  rw [laplaceK'_zero]
  field_simp
  ring

lemma laplaceK_norm_le (z : ℂ) (hz : 0 < z.re) {x₀ : ℝ} (hx₀ : 0 < x₀)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖laplaceK z x₀ t‖ ≤ (2 + 2 * t / x₀) / ‖z‖ ^ 2 := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; rw [h] at hz; simp at hz)
  have hφt : ‖laplaceφ z t - 1‖ ≤ 2 := by
    calc ‖laplaceφ z t - 1‖ ≤ ‖laplaceφ z t‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; gcongr; exact laplaceφ_norm_le z hz.le ht
      _ = 2 := by norm_num
  have hφx : ‖1 - laplaceφ z x₀‖ ≤ 2 := by
    calc ‖1 - laplaceφ z x₀‖ ≤ ‖(1:ℂ)‖ + ‖laplaceφ z x₀‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; gcongr; exact laplaceφ_norm_le z hz.le hx₀.le
      _ = 2 := by norm_num
  calc ‖laplaceK z x₀ t‖
      = ‖(laplaceφ z t - 1) / z ^ 2 + (t : ℂ) * ((1 - laplaceφ z x₀) / ((x₀ : ℂ) * z ^ 2))‖ := rfl
    _ ≤ ‖(laplaceφ z t - 1) / z ^ 2‖ + ‖(t : ℂ) * ((1 - laplaceφ z x₀) / ((x₀ : ℂ) * z ^ 2))‖ :=
        norm_add_le _ _
    _ = ‖laplaceφ z t - 1‖ / ‖z‖ ^ 2 + t * (‖1 - laplaceφ z x₀‖ / (x₀ * ‖z‖ ^ 2)) := by
        simp only [norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht, abs_of_nonneg hx₀.le]
    _ ≤ 2 / ‖z‖ ^ 2 + t * (2 / (x₀ * ‖z‖ ^ 2)) := by
        gcongr
    _ = (2 + 2 * t / x₀) / ‖z‖ ^ 2 := by
        field_simp

lemma integral_norm_laplaceK_le (z : ℂ) (hz : 0 < z.re) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∫ t in (0:ℝ)..x₀, ‖laplaceK z x₀ t‖ ≤ 3 * x₀ / ‖z‖ ^ 2 := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; rw [h] at hz; simp at hz)
  have hA1 : (∫ t in (0:ℝ)..x₀, (2:ℝ)) = 2*x₀ := by
    rw [intervalIntegral.integral_const]; simp only [smul_eq_mul, sub_zero]; ring
  have hA2 : (∫ t in (0:ℝ)..x₀, 2 * t / x₀) = x₀ := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_id]
    field_simp
    ring
  have hA : (∫ t in (0:ℝ)..x₀, (2 + 2 * t / x₀ : ℝ)) = 3 * x₀ := by
    rw [intervalIntegral.integral_add]
    · rw [hA1, hA2]; ring
    · exact continuous_const.intervalIntegrable _ _
    · exact ((continuous_const.mul continuous_id).div_const x₀).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun t => ‖laplaceK z x₀ t‖) volume (0:ℝ) x₀ :=
    (continuous_laplaceK z x₀).norm.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ => 2 + 2 * t / x₀) volume (0:ℝ) x₀ :=
    (continuous_const.add ((continuous_const.mul continuous_id).div_const x₀)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => (2 + 2 * t / x₀) / ‖z‖ ^ 2) volume (0:ℝ) x₀ :=
    hint.div_const _
  have hle := intervalIntegral.integral_mono_on hx₀.le h1 h2
    (fun t ht => laplaceK_norm_le z hz hx₀ ht.1)
  refine hle.trans_eq ?_
  rw [intervalIntegral.integral_div, hA]

theorem laplace_F0_bound {x₀ B : ℝ} (hx₀ : 0 < x₀) {f f' f'' : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc (0:ℝ) x₀, HasDerivAt f (f' t) t)
    (hd' : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt f' (f'' t) t)
    (hf'' : ContinuousOn f'' (Set.Icc (0:ℝ) x₀))
    (hb : ∀ t ∈ Set.Icc (0:ℝ) x₀, |f'' t| ≤ B)
    (hx : f x₀ = 0)
    {z : ℂ} (hz : 0 < z.re) :
    ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * (f t : ℂ)) - (f 0 : ℂ) / z‖
      ≤ (1 / ‖z‖ ^ 2) * (3 * B * x₀ + 2 * |f 0| / x₀) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hx₀ne : x₀ ≠ 0 := ne_of_gt hx₀
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb 0 ⟨le_refl 0, hx₀.le⟩)
  set F : ℝ → ℂ := fun t => laplaceK' z x₀ t * (f t : ℂ) - laplaceK z x₀ t * (f' t : ℂ) with hF
  set G : ℝ → ℂ := fun t => laplaceφ z t * (f t : ℂ) - laplaceK z x₀ t * (f'' t : ℂ) with hG
  -- boundedness of f' on (0,x₀)
  have hfbdd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖f' t‖ ≤ ‖f' (x₀/2)‖ + B * x₀ := by
    intro t ht
    have hthalf : x₀/2 ∈ Set.Ioo (0:ℝ) x₀ := ⟨by linarith, by linarith⟩
    have hcont : ∀ s ∈ Set.Ioo (0:ℝ) x₀, HasDerivWithinAt f' (f'' s) (Set.Ioo 0 x₀) s :=
      fun s hs => (hd' s hs).hasDerivWithinAt
    have hbound : ∀ s ∈ Set.Ioo (0:ℝ) x₀, ‖f'' s‖ ≤ B := by
      intro s hs
      rw [Real.norm_eq_abs]
      exact hb s ⟨hs.1.le, hs.2.le⟩
    have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hcont hbound
      (convex_Ioo 0 x₀) ht hthalf
    have hlip' : ‖f' t - f' (x₀/2)‖ ≤ B * ‖t - x₀/2‖ := by
      simpa only [norm_sub_rev] using hlip
    have hdist : ‖t - x₀/2‖ ≤ x₀ := by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc ‖f' t‖ ≤ ‖f' t - f' (x₀/2)‖ + ‖f' (x₀/2)‖ := by
          have := norm_add_le (f' t - f' (x₀/2)) (f' (x₀/2))
          rwa [sub_add_cancel] at this
      _ ≤ B * ‖t - x₀/2‖ + ‖f' (x₀/2)‖ := by gcongr
      _ ≤ B * x₀ + ‖f' (x₀/2)‖ := by gcongr
      _ = ‖f' (x₀/2)‖ + B * x₀ := by ring
  -- derivative of F is G
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt F (G t) t := by
    intro t ht
    have htI : t ∈ Set.Icc (0:ℝ) x₀ := ⟨ht.1.le, ht.2.le⟩
    have hk : HasDerivAt (laplaceK z x₀) (laplaceK' z x₀ t) t := laplaceK_hasDerivAt z hz0 x₀ t
    have hk' : HasDerivAt (laplaceK' z x₀) (laplaceφ z t) t := laplaceK'_hasDerivAt z hz0 x₀ t
    have hf1 : HasDerivAt (fun s : ℝ => (f s : ℂ)) ((f' t : ℝ) : ℂ) t := (hd t htI).ofReal_comp
    have hf2 : HasDerivAt (fun s : ℝ => (f' s : ℂ)) ((f'' t : ℝ) : ℂ) t := (hd' t ht).ofReal_comp
    have h1 : HasDerivAt (fun s : ℝ => laplaceK' z x₀ s * (f s : ℂ))
        (laplaceφ z t * (f t : ℂ) + laplaceK' z x₀ t * (f' t : ℂ)) t := hk'.mul hf1
    have h2 : HasDerivAt (fun s : ℝ => laplaceK z x₀ s * (f' s : ℂ))
        (laplaceK' z x₀ t * (f' t : ℂ) + laplaceK z x₀ t * (f'' t : ℂ)) t := hk.mul hf2
    have hsub := h1.sub h2
    have hder : (laplaceφ z t * (f t : ℂ) + laplaceK' z x₀ t * (f' t : ℂ))
        - (laplaceK' z x₀ t * (f' t : ℂ) + laplaceK z x₀ t * (f'' t : ℂ)) = G t := by
      rw [hG]; ring
    exact hsub.congr_deriv hder
  -- continuity/integrability of G, and of the pieces
  have hfcont : ContinuousOn f (Set.Icc (0:ℝ) x₀) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hcG : ContinuousOn G (Set.Icc (0:ℝ) x₀) := by
    rw [hG]
    exact ((continuous_laplaceφ z).continuousOn.mul
        (Complex.continuous_ofReal.comp_continuousOn hfcont)).sub
      ((continuous_laplaceK z x₀).continuousOn.mul
        (Complex.continuous_ofReal.comp_continuousOn hf''))
  have hIntG : IntervalIntegrable G volume (0:ℝ) x₀ := by
    rw [← Set.uIcc_of_le hx₀.le] at hcG
    exact hcG.intervalIntegrable
  -- limit of F at 0
  have hbdd0 : IsBoundedUnder (· ≤ ·) (𝓝[>] (0:ℝ)) (fun t => ‖(f' t : ℂ)‖) := by
    apply isBoundedUnder_of_eventually_le (a := ‖f' (x₀/2)‖ + B * x₀)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx₀), self_mem_nhdsWithin] with t ht1 ht2
    rw [Complex.norm_real]
    exact hfbdd t ⟨ht2, ht1⟩
  have htend0 : Tendsto F (𝓝[>] (0:ℝ)) (𝓝 (laplaceK' z x₀ 0 * (f 0 : ℂ))) := by
    have hA : Tendsto (fun t => laplaceK' z x₀ t * (f t : ℂ)) (𝓝[>] (0:ℝ))
        (𝓝 (laplaceK' z x₀ 0 * (f 0 : ℂ))) := by
      have h1 : Tendsto (laplaceK' z x₀) (𝓝[>] (0:ℝ)) (𝓝 (laplaceK' z x₀ 0)) :=
        (continuous_laplaceK' z x₀).continuousAt.continuousWithinAt
      have h2 : Tendsto (fun t : ℝ => (f t : ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (f 0 : ℂ)) :=
        (Complex.continuous_ofReal.continuousAt.comp
          (hd 0 ⟨le_refl 0, hx₀.le⟩).continuousAt).continuousWithinAt
      exact h1.mul h2
    have hB' : Tendsto (fun t => laplaceK z x₀ t * (f' t : ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hk : Tendsto (laplaceK z x₀) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have h : ContinuousWithinAt (laplaceK z x₀) (Set.Ioi 0) 0 :=
          (continuous_laplaceK z x₀).continuousAt.continuousWithinAt
        simp only [ContinuousWithinAt, laplaceK_zero] at h
        exact h
      exact hk.zero_mul_isBoundedUnder_le hbdd0
    have hsub := hA.sub hB'
    rw [sub_zero] at hsub
    have hFeq : (fun t => laplaceK' z x₀ t * (f t : ℂ) - laplaceK z x₀ t * (f' t : ℂ)) = F := by
      rw [hF]
    rwa [hFeq] at hsub
  -- limit of F at x₀
  have hbddx : IsBoundedUnder (· ≤ ·) (𝓝[<] x₀) (fun t => ‖(f' t : ℂ)‖) := by
    apply isBoundedUnder_of_eventually_le (a := ‖f' (x₀/2)‖ + B * x₀)
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hx₀), self_mem_nhdsWithin] with t ht1 ht2
    rw [Complex.norm_real]
    exact hfbdd t ⟨ht1, ht2⟩
  have htendx : Tendsto F (𝓝[<] x₀) (𝓝 0) := by
    have hA : Tendsto (fun t => laplaceK' z x₀ t * (f t : ℂ)) (𝓝[<] x₀) (𝓝 0) := by
      have h1 : Tendsto (laplaceK' z x₀) (𝓝[<] x₀) (𝓝 (laplaceK' z x₀ x₀)) :=
        (continuous_laplaceK' z x₀).continuousAt.continuousWithinAt
      have h2 : Tendsto (fun t : ℝ => (f t : ℂ)) (𝓝[<] x₀) (𝓝 ((f x₀ : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.continuousAt.comp
          (hd x₀ ⟨hx₀.le, le_refl x₀⟩).continuousAt).continuousWithinAt
      have h := h1.mul h2
      simpa [hx] using h
    have hB' : Tendsto (fun t => laplaceK z x₀ t * (f' t : ℂ)) (𝓝[<] x₀) (𝓝 0) := by
      have hk : Tendsto (laplaceK z x₀) (𝓝[<] x₀) (𝓝 0) := by
        have h : ContinuousWithinAt (laplaceK z x₀) (Set.Iio x₀) x₀ :=
          (continuous_laplaceK z x₀).continuousAt.continuousWithinAt
        simp only [ContinuousWithinAt, laplaceK_x0 z hz0 x₀ hx₀ne] at h
        exact h
      exact hk.zero_mul_isBoundedUnder_le hbddx
    have hsub := hA.sub hB'
    rw [sub_zero] at hsub
    have hFeq : (fun t => laplaceK' z x₀ t * (f t : ℂ) - laplaceK z x₀ t * (f' t : ℂ)) = F := by
      rw [hF]
    rwa [hFeq] at hsub
  -- Fundamental theorem of calculus
  have hFTC : ∫ t in (0:ℝ)..x₀, G t = (0:ℂ) - laplaceK' z x₀ 0 * (f 0 : ℂ) :=
    integral_eq_sub_of_hasDerivAt_of_tendsto hx₀ hderiv hIntG htend0 htendx
  have hIφf : IntervalIntegrable (fun t => laplaceφ z t * (f t : ℂ)) volume (0:ℝ) x₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx₀.le]
    exact (continuous_laplaceφ z).continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn hfcont)
  have hIkf'' : IntervalIntegrable (fun t => laplaceK z x₀ t * (f'' t : ℂ)) volume (0:ℝ) x₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx₀.le]
    exact (continuous_laplaceK z x₀).continuousOn.mul
      (Complex.continuous_ofReal.comp_continuousOn hf'')
  have hsplit : ∫ t in (0:ℝ)..x₀, G t
      = (∫ t in (0:ℝ)..x₀, laplaceφ z t * (f t : ℂ))
        - (∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * (f'' t : ℂ)) := by
    rw [hG]
    exact intervalIntegral.integral_sub hIφf hIkf''
  have hFTC2 : (∫ t in (0:ℝ)..x₀, laplaceφ z t * (f t : ℂ))
      - (∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * (f'' t : ℂ)) = -(laplaceK' z x₀ 0 * (f 0 : ℂ)) := by
    rw [← hsplit, hFTC, zero_sub]
  have hkey : (∫ t in (0:ℝ)..x₀, laplaceφ z t * (f t : ℂ)) - (f 0 : ℂ) / z
      = (f 0 : ℂ) * ((laplaceφ z x₀ - 1) / ((x₀ : ℂ) * z ^ 2))
        + ∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * (f'' t : ℂ) := by
    have h1 : (∫ t in (0:ℝ)..x₀, laplaceφ z t * (f t : ℂ))
        = (∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * (f'' t : ℂ)) - laplaceK' z x₀ 0 * (f 0 : ℂ) := by
      linear_combination hFTC2
    rw [h1]
    rw [show ((∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * (f'' t : ℂ)) - laplaceK' z x₀ 0 * (f 0 : ℂ))
          - (f 0 : ℂ)/z
        = (f 0 : ℂ) * (-laplaceK' z x₀ 0 - 1/z)
          + ∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * (f'' t : ℂ) from by ring]
    rw [laplaceK'_zero_key z hz0 x₀ hx₀ne]
  -- bounds for the two terms
  have hφx_le : ‖laplaceφ z x₀ - 1‖ ≤ 2 := by
    calc ‖laplaceφ z x₀ - 1‖ ≤ ‖laplaceφ z x₀‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; gcongr; exact laplaceφ_norm_le z hz.le hx₀.le
      _ = 2 := by norm_num
  have hbound1 : ‖(f 0 : ℂ) * ((laplaceφ z x₀ - 1) / ((x₀ : ℂ) * z ^ 2))‖
      ≤ 2 * |f 0| / (x₀ * ‖z‖ ^ 2) := by
    rw [norm_mul, norm_div]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx₀.le]
    calc ‖f 0‖ * (‖laplaceφ z x₀ - 1‖ / (x₀ * ‖z‖ ^ 2))
        ≤ |f 0| * (2 / (x₀ * ‖z‖ ^ 2)) := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hφx_le (by positivity))
            (abs_nonneg _)
      _ = 2 * |f 0| / (x₀ * ‖z‖ ^ 2) := by ring
  have hbound2 : ‖∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * (f'' t : ℂ)‖
      ≤ B * (3 * x₀ / ‖z‖ ^ 2) := by
    have h1 : IntervalIntegrable (fun t => ‖laplaceK z x₀ t * (f'' t : ℂ)‖) volume (0:ℝ) x₀ := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx₀.le]
      exact ((continuous_laplaceK z x₀).continuousOn.mul
        (Complex.continuous_ofReal.comp_continuousOn hf'')).norm
    have h2 : IntervalIntegrable (fun t => ‖laplaceK z x₀ t‖ * B) volume (0:ℝ) x₀ :=
      ((continuous_laplaceK z x₀).norm.mul continuous_const).intervalIntegrable _ _
    calc ‖∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * (f'' t : ℂ)‖
        ≤ ∫ t in (0:ℝ)..x₀, ‖laplaceK z x₀ t * (f'' t : ℂ)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx₀.le
      _ ≤ ∫ t in (0:ℝ)..x₀, ‖laplaceK z x₀ t‖ * B := by
          apply intervalIntegral.integral_mono_on hx₀.le h1 h2
          intro t ht
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hb t ht) (norm_nonneg _)
      _ = B * ∫ t in (0:ℝ)..x₀, ‖laplaceK z x₀ t‖ := by
          rw [intervalIntegral.integral_mul_const]; ring
      _ ≤ B * (3 * x₀ / ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (integral_norm_laplaceK_le z hz hx₀) hB
  -- final assembly
  have hφint : (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * (f t : ℂ))
      = ∫ t in (0:ℝ)..x₀, laplaceφ z t * (f t : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    show Complex.exp (-(z * (t : ℂ))) * (f t : ℂ) = laplaceφ z t * (f t : ℂ)
    rw [laplaceφ_apply]
  rw [hφint, hkey]
  calc ‖(f 0 : ℂ) * ((laplaceφ z x₀ - 1) / ((x₀ : ℂ) * z ^ 2))
        + ∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * (f'' t : ℂ)‖
      ≤ ‖(f 0 : ℂ) * ((laplaceφ z x₀ - 1) / ((x₀ : ℂ) * z ^ 2))‖
        + ‖∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * (f'' t : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * |f 0| / (x₀ * ‖z‖ ^ 2) + B * (3 * x₀ / ‖z‖ ^ 2) := add_le_add hbound1 hbound2
    _ = (1 / ‖z‖ ^ 2) * (3 * B * x₀ + 2 * |f 0| / x₀) := by
        field_simp
        ring

end Commons.Analysis.Integral