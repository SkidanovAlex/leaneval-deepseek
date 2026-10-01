import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Integral.laplace_F0_bound

namespace Commons.Analysis.Integral

open MeasureTheory intervalIntegral Filter
open scoped Topology

/-- Auxiliary complex-valued version of the Laplace bound: if `f` is continuous on `[0,x₀]`,
`C²` on `(0,x₀)` (through explicit derivative functions `f1, f2`), bounded second derivative
`‖f2‖ ≤ B`, and `f 0 = f x₀ = 0`, then the Laplace transform of `f` is bounded by
`(1/‖z‖²)·(3·B·x₀)` for `Re z > 0`. -/
theorem laplace_bound_C2 {x₀ B : ℝ} (hx₀ : 0 < x₀) {f f1 f2 : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc (0:ℝ) x₀))
    (hd1 : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt f (f1 t) t)
    (hd2 : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt f1 (f2 t) t)
    (hf2cont : ContinuousOn f2 (Set.Ioo (0:ℝ) x₀))
    (hb : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖f2 t‖ ≤ B)
    (hx : f x₀ = 0) (hx0 : f 0 = 0)
    {z : ℂ} (hz : 0 < z.re) :
    ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t‖ ≤ (1 / ‖z‖ ^ 2) * (3 * B * x₀) := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hb (x₀/2) ⟨by linarith, by linarith⟩)
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hx₀ne : x₀ ≠ 0 := ne_of_gt hx₀
  set F : ℝ → ℂ := fun t => laplaceK' z x₀ t * f t - laplaceK z x₀ t * f1 t with hF
  set G : ℝ → ℂ := fun t => laplaceφ z t * f t - laplaceK z x₀ t * f2 t with hG
  -- bound on `f1` on `(0,x₀)`
  have hfbdd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖f1 t‖ ≤ ‖f1 (x₀/2)‖ + B * x₀ := by
    intro t ht
    have hthalf : x₀/2 ∈ Set.Ioo (0:ℝ) x₀ := ⟨by linarith, by linarith⟩
    have hcont' : ∀ s ∈ Set.Ioo (0:ℝ) x₀, HasDerivWithinAt f1 (f2 s) (Set.Ioo 0 x₀) s :=
      fun s hs => (hd2 s hs).hasDerivWithinAt
    have hbound' : ∀ s ∈ Set.Ioo (0:ℝ) x₀, ‖f2 s‖ ≤ B := hb
    have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hcont' hbound'
      (convex_Ioo 0 x₀) ht hthalf
    have hlip' : ‖f1 t - f1 (x₀/2)‖ ≤ B * ‖t - x₀/2‖ := by
      simpa only [norm_sub_rev] using hlip
    have hdist : ‖t - x₀/2‖ ≤ x₀ := by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc ‖f1 t‖ ≤ ‖f1 t - f1 (x₀/2)‖ + ‖f1 (x₀/2)‖ := by
          have := norm_add_le (f1 t - f1 (x₀/2)) (f1 (x₀/2)); rwa [sub_add_cancel] at this
      _ ≤ B * ‖t - x₀/2‖ + ‖f1 (x₀/2)‖ := by gcongr
      _ ≤ B * x₀ + ‖f1 (x₀/2)‖ := by gcongr
      _ = ‖f1 (x₀/2)‖ + B * x₀ := by ring
  -- bound on `f` on `(0,x₀)`
  have hfbd : ∀ t ∈ Set.Ioo (0:ℝ) x₀,
      ‖f t‖ ≤ ‖f (x₀/2)‖ + (‖f1 (x₀/2)‖ + B * x₀) * x₀ := by
    intro t ht
    have hthalf : x₀/2 ∈ Set.Ioo (0:ℝ) x₀ := ⟨by linarith, by linarith⟩
    have hcont' : ∀ s ∈ Set.Ioo (0:ℝ) x₀, HasDerivWithinAt f (f1 s) (Set.Ioo 0 x₀) s :=
      fun s hs => (hd1 s hs).hasDerivWithinAt
    have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hcont' hfbdd
      (convex_Ioo 0 x₀) ht hthalf
    have hlip' : ‖f t - f (x₀/2)‖ ≤ (‖f1 (x₀/2)‖ + B * x₀) * ‖t - x₀/2‖ := by
      simpa only [norm_sub_rev] using hlip
    have hdist : ‖t - x₀/2‖ ≤ x₀ := by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hC1 : 0 ≤ ‖f1 (x₀/2)‖ + B * x₀ :=
      add_nonneg (norm_nonneg _) (mul_nonneg hB hx₀.le)
    calc ‖f t‖ ≤ ‖f t - f (x₀/2)‖ + ‖f (x₀/2)‖ := by
          have := norm_add_le (f t - f (x₀/2)) (f (x₀/2)); rwa [sub_add_cancel] at this
      _ ≤ (‖f1 (x₀/2)‖ + B * x₀) * ‖t - x₀/2‖ + ‖f (x₀/2)‖ := by gcongr
      _ ≤ (‖f1 (x₀/2)‖ + B * x₀) * x₀ + ‖f (x₀/2)‖ :=
          add_le_add (mul_le_mul_of_nonneg_left hdist hC1) le_rfl
      _ = ‖f (x₀/2)‖ + (‖f1 (x₀/2)‖ + B * x₀) * x₀ := by ring
  -- derivative identity
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt F (G t) t := by
    intro t ht
    have hk : HasDerivAt (laplaceK z x₀) (laplaceK' z x₀ t) t := laplaceK_hasDerivAt z hz0 x₀ t
    have hk' : HasDerivAt (laplaceK' z x₀) (laplaceφ z t) t := laplaceK'_hasDerivAt z hz0 x₀ t
    have hf1' : HasDerivAt f (f1 t) t := hd1 t ht
    have hf2' : HasDerivAt f1 (f2 t) t := hd2 t ht
    have h1 : HasDerivAt (fun s => laplaceK' z x₀ s * f s)
        (laplaceφ z t * f t + laplaceK' z x₀ t * f1 t) t := hk'.mul hf1'
    have h2 : HasDerivAt (fun s => laplaceK z x₀ s * f1 s)
        (laplaceK' z x₀ t * f1 t + laplaceK z x₀ t * f2 t) t := hk.mul hf2'
    have hsub := h1.sub h2
    have hder : (laplaceφ z t * f t + laplaceK' z x₀ t * f1 t)
        - (laplaceK' z x₀ t * f1 t + laplaceK z x₀ t * f2 t) = G t := by
      rw [hG]; ring
    exact hsub.congr_deriv hder
  -- continuity of `G` on the open interval
  have hfcontIoo : ContinuousOn f (Set.Ioo (0:ℝ) x₀) :=
    hcont.mono (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  have hGcont : ContinuousOn G (Set.Ioo (0:ℝ) x₀) := by
    rw [hG]
    exact ((continuous_laplaceφ z).continuousOn.mul hfcontIoo).sub
      ((continuous_laplaceK z x₀).continuousOn.mul hf2cont)
  -- bound on `laplaceK` on `(0,x₀)`
  have hk_le : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖laplaceK z x₀ t‖ ≤ 4 / ‖z‖ ^ 2 := by
    intro t ht
    have hbase := laplaceK_norm_le z hz hx₀ ht.1.le
    have hnum : (2 + 2 * t / x₀) ≤ 4 := by
      have h1 : 2 * t / x₀ ≤ 2 := by rw [div_le_iff₀ hx₀]; linarith [ht.2]
      linarith
    calc ‖laplaceK z x₀ t‖ ≤ (2 + 2 * t / x₀) / ‖z‖ ^ 2 := hbase
      _ ≤ 4 / ‖z‖ ^ 2 := div_le_div_of_nonneg_right hnum (by positivity)
  have hz2pos : 0 < 4 / ‖z‖ ^ 2 := by positivity
  -- boundedness of G on the open interval
  have hGbound : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖G t‖ ≤
      ‖f (x₀/2)‖ + (‖f1 (x₀/2)‖ + B * x₀) * x₀ + 4 * B / ‖z‖ ^ 2 := by
    intro t ht
    rw [hG]
    have h1 : ‖laplaceφ z t * f t‖ ≤ 1 * ‖f t‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (laplaceφ_norm_le z hz.le ht.1.le) (norm_nonneg _)
    have h2 : ‖laplaceK z x₀ t * f2 t‖ ≤ (4 / ‖z‖ ^ 2) * B := by
      rw [norm_mul]
      exact mul_le_mul (hk_le t ht) (hb t ht) (norm_nonneg _) (le_of_lt hz2pos)
    calc ‖laplaceφ z t * f t - laplaceK z x₀ t * f2 t‖
        ≤ ‖laplaceφ z t * f t‖ + ‖laplaceK z x₀ t * f2 t‖ := norm_sub_le _ _
      _ ≤ 1 * ‖f t‖ + (4 / ‖z‖ ^ 2) * B := add_le_add h1 h2
      _ ≤ (‖f (x₀/2)‖ + (‖f1 (x₀/2)‖ + B * x₀) * x₀) + 4 * B / ‖z‖ ^ 2 := by
          have h1' := hfbd t ht
          have heq : (4 / ‖z‖ ^ 2) * B = 4 * B / ‖z‖ ^ 2 := by ring
          linarith [h1', heq]
  -- interval-integrability of G
  have hvol : volume (Set.Ioo (0:ℝ) x₀) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hGint : IntervalIntegrable G volume (0:ℝ) x₀ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx₀.le]
    refine IntegrableOn.of_bound (μ := volume) (s := Set.Ioo (0:ℝ) x₀) hvol
      (hGcont.aestronglyMeasurable measurableSet_Ioo)
      (‖f (x₀/2)‖ + (‖f1 (x₀/2)‖ + B * x₀) * x₀ + 4 * B / ‖z‖ ^ 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hGbound t ht
  -- interval-integrability of the two pieces
  have hIφf : IntervalIntegrable (fun t => laplaceφ z t * f t) volume (0:ℝ) x₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx₀.le]
    exact (continuous_laplaceφ z).continuousOn.mul hcont
  have hk2_le : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖laplaceK z x₀ t * f2 t‖ ≤ 4 * B / ‖z‖ ^ 2 := by
    intro t ht
    rw [norm_mul]
    calc ‖laplaceK z x₀ t‖ * ‖f2 t‖ ≤ (4 / ‖z‖ ^ 2) * B :=
          mul_le_mul (hk_le t ht) (hb t ht) (norm_nonneg _) (le_of_lt hz2pos)
      _ = 4 * B / ‖z‖ ^ 2 := by ring
  have hIkf2 : IntervalIntegrable (fun t => laplaceK z x₀ t * f2 t) volume (0:ℝ) x₀ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx₀.le]
    refine IntegrableOn.of_bound (μ := volume) (s := Set.Ioo (0:ℝ) x₀) hvol
      (((continuous_laplaceK z x₀).continuousOn.mul hf2cont).aestronglyMeasurable measurableSet_Ioo)
      (4 * B / ‖z‖ ^ 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hk2_le t ht
  -- endpoint limits of `f`
  have hf0tend : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) := by
    have h1 : Tendsto f (𝓝[Set.Icc (0:ℝ) x₀] 0) (𝓝 (f 0)) :=
      hcont.continuousWithinAt ⟨le_refl 0, hx₀.le⟩
    have h2 : 𝓝[>] (0:ℝ) ≤ 𝓝[Set.Icc (0:ℝ) x₀] 0 := by
      rw [nhdsWithin_Icc_eq_nhdsGE hx₀]
      exact nhdsWithin_mono 0 Set.Ioi_subset_Ici_self
    exact h1.mono_left h2
  have hfx₀tend : Tendsto f (𝓝[<] x₀) (𝓝 (f x₀)) := by
    have h1 : Tendsto f (𝓝[Set.Icc (0:ℝ) x₀] x₀) (𝓝 (f x₀)) :=
      hcont.continuousWithinAt ⟨hx₀.le, le_refl x₀⟩
    have h2 : 𝓝[<] x₀ ≤ 𝓝[Set.Icc (0:ℝ) x₀] x₀ := by
      rw [nhdsWithin_Icc_eq_nhdsLE hx₀]
      exact nhdsWithin_mono x₀ Set.Iio_subset_Iic_self
    exact h1.mono_left h2
  -- boundedness of f1 near endpoints
  have hbdd0 : IsBoundedUnder (· ≤ ·) (𝓝[>] (0:ℝ)) (fun t => ‖f1 t‖) := by
    apply isBoundedUnder_of_eventually_le (a := ‖f1 (x₀/2)‖ + B * x₀)
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx₀), self_mem_nhdsWithin] with t ht1 ht2
    exact hfbdd t ⟨ht2, ht1⟩
  have hbddx : IsBoundedUnder (· ≤ ·) (𝓝[<] x₀) (fun t => ‖f1 t‖) := by
    apply isBoundedUnder_of_eventually_le (a := ‖f1 (x₀/2)‖ + B * x₀)
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hx₀), self_mem_nhdsWithin] with t ht1 ht2
    exact hfbdd t ⟨ht1, ht2⟩
  have htend0 : Tendsto F (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hA : Tendsto (fun t => laplaceK' z x₀ t * f t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h1 : Tendsto (laplaceK' z x₀) (𝓝[>] (0:ℝ)) (𝓝 (laplaceK' z x₀ 0)) :=
        (continuous_laplaceK' z x₀).continuousAt.continuousWithinAt
      have h := h1.mul hf0tend
      simpa [hx0] using h
    have hB' : Tendsto (fun t => laplaceK z x₀ t * f1 t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hk : Tendsto (laplaceK z x₀) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have h : ContinuousWithinAt (laplaceK z x₀) (Set.Ioi 0) 0 :=
          (continuous_laplaceK z x₀).continuousAt.continuousWithinAt
        simpa only [ContinuousWithinAt, laplaceK_zero] using h
      exact hk.zero_mul_isBoundedUnder_le hbdd0
    have hsub := hA.sub hB'
    rw [sub_zero] at hsub
    have hFeq : (fun t => laplaceK' z x₀ t * f t - laplaceK z x₀ t * f1 t) = F := by rw [hF]
    rwa [hFeq] at hsub
  have htendx : Tendsto F (𝓝[<] x₀) (𝓝 0) := by
    have hA : Tendsto (fun t => laplaceK' z x₀ t * f t) (𝓝[<] x₀) (𝓝 0) := by
      have h1 : Tendsto (laplaceK' z x₀) (𝓝[<] x₀) (𝓝 (laplaceK' z x₀ x₀)) :=
        (continuous_laplaceK' z x₀).continuousAt.continuousWithinAt
      have h := h1.mul hfx₀tend
      simpa [hx] using h
    have hB' : Tendsto (fun t => laplaceK z x₀ t * f1 t) (𝓝[<] x₀) (𝓝 0) := by
      have hk : Tendsto (laplaceK z x₀) (𝓝[<] x₀) (𝓝 0) := by
        have h : ContinuousWithinAt (laplaceK z x₀) (Set.Iio x₀) x₀ :=
          (continuous_laplaceK z x₀).continuousAt.continuousWithinAt
        simpa only [ContinuousWithinAt, laplaceK_x0 z hz0 x₀ hx₀ne] using h
      exact hk.zero_mul_isBoundedUnder_le hbddx
    have hsub := hA.sub hB'
    rw [sub_zero] at hsub
    have hFeq : (fun t => laplaceK' z x₀ t * f t - laplaceK z x₀ t * f1 t) = F := by rw [hF]
    rwa [hFeq] at hsub
  -- fundamental theorem of calculus
  have hFTC : (∫ t in (0:ℝ)..x₀, G t) = 0 := by
    have h := integral_eq_sub_of_hasDerivAt_of_tendsto hx₀ hderiv hGint htend0 htendx
    rw [sub_self] at h
    exact h
  have hsplit : (∫ t in (0:ℝ)..x₀, G t)
      = (∫ t in (0:ℝ)..x₀, laplaceφ z t * f t)
        - (∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * f2 t) := by
    rw [hG]
    exact intervalIntegral.integral_sub hIφf hIkf2
  have hkey : (∫ t in (0:ℝ)..x₀, laplaceφ z t * f t)
      = ∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * f2 t := by
    rw [hsplit] at hFTC
    exact sub_eq_zero.mp hFTC
  have hφint : (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t)
      = ∫ t in (0:ℝ)..x₀, laplaceφ z t * f t := by
    apply intervalIntegral.integral_congr
    intro t _
    show Complex.exp (-(z * (t : ℂ))) * f t = laplaceφ z t * f t
    rw [laplaceφ_apply]
  rw [hφint, hkey]
  -- final bound
  have h1 : IntervalIntegrable (fun t => ‖laplaceK z x₀ t * f2 t‖) volume (0:ℝ) x₀ := hIkf2.norm
  have hkint : IntervalIntegrable (fun t => ‖laplaceK z x₀ t‖) volume (0:ℝ) x₀ :=
    (continuous_laplaceK z x₀).norm.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => ‖laplaceK z x₀ t‖ * B) volume (0:ℝ) x₀ :=
    hkint.mul_const B
  have hbound2 : ‖∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * f2 t‖ ≤ B * (3 * x₀ / ‖z‖ ^ 2) := by
    calc ‖∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * f2 t‖
        ≤ ∫ t in (0:ℝ)..x₀, ‖laplaceK z x₀ t * f2 t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hx₀.le
      _ ≤ ∫ t in (0:ℝ)..x₀, ‖laplaceK z x₀ t‖ * B := by
          apply intervalIntegral.integral_mono_on hx₀.le h1 h2
          intro t ht
          rw [norm_mul]
          by_cases ht0 : t = 0
          · rw [ht0]; simp [laplaceK_zero]
          by_cases htx : t = x₀
          · rw [htx, laplaceK_x0 z hz0 x₀ hx₀ne]; simp
          · exact mul_le_mul_of_nonneg_left
              (hb t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htx⟩) (norm_nonneg _)
      _ = B * ∫ t in (0:ℝ)..x₀, ‖laplaceK z x₀ t‖ := by
          rw [intervalIntegral.integral_mul_const]; ring
      _ ≤ B * (3 * x₀ / ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (integral_norm_laplaceK_le z hz hx₀) hB
  calc ‖∫ t in (0:ℝ)..x₀, laplaceK z x₀ t * f2 t‖ ≤ B * (3 * x₀ / ‖z‖ ^ 2) := hbound2
    _ = (1 / ‖z‖ ^ 2) * (3 * B * x₀) := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring

theorem laplace_bound_piecewiseC2 {x₀ B : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc (0:ℝ) x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo (0:ℝ) x₀))
    (hb : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hx : f x₀ = 0) (hx0 : f 0 = 0)
    {z : ℂ} (hz : 0 < z.re) :
    ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t‖ ≤ (1 / ‖z‖ ^ 2) * (3 * B * x₀) := by
  refine laplace_bound_C2 (f := f) (f1 := deriv f) (f2 := iteratedDeriv 2 f)
    hx₀ hcont ?_ ?_ ?_ hb hx hx0 hz
  · intro t ht
    exact (hf2.differentiableOn (by norm_num)).hasDerivAt (Ioo_mem_nhds ht.1 ht.2)
  · intro t ht
    have hdiff : DifferentiableOn ℝ (deriv f) (Set.Ioo (0:ℝ) x₀) := by
      have h := hf2.differentiableOn_iteratedDerivWithin (m := 1) (by norm_num)
        (uniqueDiffOn_Ioo 0 x₀)
      refine h.congr ?_
      intro y hy
      rw [iteratedDerivWithin_one, derivWithin_of_isOpen isOpen_Ioo hy]
    have hd := hdiff.hasDerivAt (Ioo_mem_nhds ht.1 ht.2)
    have heq : deriv (deriv f) t = iteratedDeriv 2 f t := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
    rwa [heq] at hd
  · have h := hf2.continuousOn_iteratedDerivWithin (m := 2) (le_refl _) (uniqueDiffOn_Ioo 0 x₀)
    refine h.congr ?_
    intro y hy
    exact (iteratedDerivWithin_of_isOpen isOpen_Ioo hy).symm

end Commons.Analysis.Integral