import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Fourier.Inversion
import Submission.Commons.Analysis.Integral.laplace_bound_piecewiseC2

open MeasureTheory Filter
open scoped Topology FourierTransform RealInnerProductSpace

namespace Commons.Analysis.Fourier

/-- Integrability on `ℝ` of `(A + (y/c - d)^2)⁻¹` for `A > 0` and `c ≠ 0`. -/
private theorem integrable_inv_sq_affine {A c d : ℝ} (hA : 0 < A) (hc : c ≠ 0) :
    Integrable (fun y : ℝ => (A + (y/c - d)^2)⁻¹) volume := by
  set K' : ℝ := max ((1 + 2*c^2*d^2)/A) (2*c^2) with hK'
  have hK'pos : 0 < K' := by
    have h1 : 0 < (1 + 2*c^2*d^2)/A := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  have hK'ge1 : (1 + 2*c^2*d^2)/A ≤ K' := le_max_left _ _
  have hK'ge2 : 2*c^2 ≤ K' := le_max_right _ _
  have hg : Integrable (fun y : ℝ => K' * (1 + y^2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul K'
  refine hg.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.inv₀
    · fun_prop
    · intro y
      have : 0 < A + (y/c - d)^2 := by nlinarith [sq_nonneg (y/c - d), hA]
      positivity
  · filter_upwards with y
    have hden : 0 < A + (y/c - d)^2 := by nlinarith [sq_nonneg (y/c - d), hA]
    have h1y : 0 < 1 + y^2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hden.le)]
    rw [inv_eq_one_div, ← div_eq_mul_inv]
    rw [div_le_div_iff₀ hden h1y]
    have hz : y = c * (y/c - d) + c*d := by field_simp; ring
    have hbound : (1 + y^2) ≤ (1 + 2*c^2*d^2) + 2*c^2*(y/c - d)^2 := by
      have h2 : y^2 = (c*(y/c - d) + c*d)^2 := by rw [← hz]
      rw [h2]
      nlinarith [sq_nonneg (c*(y/c-d) - c*d), sq_nonneg (c*(y/c-d) + c*d), sq_nonneg c, sq_nonneg d, sq_nonneg (y/c-d)]
    have hKA : (1 + 2*c^2*d^2) ≤ K'*A := by
      have := (div_le_iff₀ hA).mp hK'ge1
      linarith [this]
    have hKz : 2*c^2*(y/c-d)^2 ≤ K'*(y/c-d)^2 :=
      mul_le_mul_of_nonneg_right hK'ge2 (sq_nonneg _)
    calc (1:ℝ)*(1 + y^2) ≤ (1 + 2*c^2*d^2) + 2*c^2*(y/c - d)^2 := by linarith [hbound]
      _ ≤ K'*A + K'*(y/c-d)^2 := add_le_add hKA hKz
      _ = K' * (A + (y/c-d)^2) := by ring

/-- The Fourier transform of an integrable function is continuous. -/
private lemma continuous_fourier {H : ℝ → ℂ} (hH : Integrable H) : Continuous (𝓕 H) := by
  rw [show 𝓕 H = VectorFourier.fourierIntegral (Real.fourierChar) volume (innerₗ ℝ) H from rfl]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hH

/-- The function `v ↦ exp(-(u L v)) f v` cut off to `[0, x₀]` has Fourier transform given by
the vertical Laplace integral. -/
private lemma fourier_id {x₀ : ℝ} {f : ℝ → ℂ} {u : ℂ} {L : ℝ} (hx₀ : 0 < x₀) (t : ℝ) :
    𝓕 (Set.indicator (Set.Icc 0 x₀) (fun v => Complex.exp (-(u * (L:ℂ) * (v:ℂ))) * f v))
      ((-L / (2 * Real.pi)) * t)
    = ∫ v in (0:ℝ)..x₀, Complex.exp (-((u - (t:ℂ)*Complex.I) * (L:ℂ) * (v:ℂ))) * f v := by
  rw [Real.fourier_eq']
  trans ∫ v, Set.indicator (Set.Icc 0 x₀)
      (fun v => Complex.exp (-((u - (t:ℂ)*Complex.I) * (L:ℂ) * (v:ℂ))) * f v) v
  · apply integral_congr_ae
    filter_upwards with v
    by_cases hv : v ∈ Set.Icc 0 x₀
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
      simp only [smul_eq_mul]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      simp only [Real.inner_apply]
      push_cast
      field_simp
      ring_nf
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
      simp
  · rw [integral_indicator measurableSet_Icc]
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hx₀.le]

theorem vertical_laplace_eq_zero {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {u : ℂ} (hu : 0 < u.re) {L : ℝ} (hL : 0 < L) :
    (∫ t : ℝ, ∫ v : ℝ in (0:ℝ)..x₀,
        Complex.exp (-((u - (t : ℂ) * Complex.I) * (L : ℂ) * (v : ℂ))) * f v) = 0 := by
  have hfx₀ : f x₀ = 0 := hvan x₀ le_rfl
  set c : ℝ := -L / (2 * Real.pi) with hc
  have hcne : c ≠ 0 := by
    rw [hc]; apply div_ne_zero
    · linarith
    · positivity
  let F : ℝ → ℂ := fun t => ∫ v : ℝ in (0:ℝ)..x₀,
      Complex.exp (-((u - (t:ℂ)*Complex.I) * (L:ℂ) * (v:ℂ))) * f v
  set H : ℝ → ℂ := Set.indicator (Set.Icc 0 x₀)
      (fun v => Complex.exp (-(u * (L:ℂ) * (v:ℂ))) * f v) with hH
  have hH0 : H 0 = 0 := by
    rw [hH, Set.indicator_of_mem (show (0:ℝ) ∈ Set.Icc 0 x₀ from ⟨le_refl 0, hx₀.le⟩)]
    simp [hf0]
  -- Pointwise Fourier identification
  have hFid : ∀ t : ℝ, F t = 𝓕 H (c * t) := by
    intro t
    rw [hH, hc]
    exact (fourier_id hx₀ t).symm
  -- Continuity of H at 0
  have hHcont0 : ContinuousAt H 0 := by
    change Tendsto H (𝓝 0) (𝓝 (H 0))
    rw [hH0]
    have hle : Tendsto H (𝓝[≤] (0:ℝ)) (𝓝 0) := by
      have hev : H =ᶠ[𝓝[≤] (0:ℝ)] (fun _ => (0:ℂ)) := by
        filter_upwards [self_mem_nhdsWithin] with v hv
        rcases eq_or_lt_of_le (Set.mem_Iic.mp hv) with h0 | hlt
        · rw [h0]; exact hH0
        · rw [hH]; exact Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hlt)) _
      exact tendsto_const_nhds.congr' hev.symm
    have hgt : Tendsto H (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hev : H =ᶠ[𝓝[>] (0:ℝ)]
          (fun v => Complex.exp (-(u * (L:ℂ) * (v:ℂ))) * f v) := by
        filter_upwards [Ioo_mem_nhdsGT hx₀] with v hv
        rw [hH, Set.indicator_of_mem (Set.mem_Icc.mpr ⟨le_of_lt hv.1, le_of_lt hv.2⟩)]
      have hftend : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) := by
        have h1 : Tendsto f (𝓝[Set.Icc 0 x₀] 0) (𝓝 (f 0)) :=
          hcont.continuousWithinAt ⟨le_refl 0, hx₀.le⟩
        have h2 : 𝓝[>] (0:ℝ) ≤ 𝓝[Set.Icc 0 x₀] 0 := by
          rw [nhdsWithin_Icc_eq_nhdsGE hx₀]
          exact nhdsWithin_mono 0 Set.Ioi_subset_Ici_self
        exact h1.mono_left h2
      have heKtend : Tendsto (fun v : ℝ => Complex.exp (-(u * (L:ℂ) * (v:ℂ))))
          (𝓝[>] (0:ℝ)) (𝓝 1) := by
        have hc' : Continuous (fun v : ℝ => Complex.exp (-(u * (L:ℂ) * (v:ℂ)))) := by fun_prop
        have hthis : Tendsto (fun v : ℝ => Complex.exp (-(u * (L:ℂ) * (v:ℂ)))) (𝓝 (0:ℝ))
            (𝓝 (Complex.exp (-(u * (L:ℂ) * ((0:ℝ):ℂ))))) := hc'.continuousAt
        have hval : Complex.exp (-(u * (L:ℂ) * ((0:ℝ):ℂ))) = 1 := by simp
        rw [hval] at hthis
        exact hthis.mono_left nhdsWithin_le_nhds
      have hKtend : Tendsto (fun v : ℝ => Complex.exp (-(u * (L:ℂ) * (v:ℂ))) * f v)
          (𝓝[>] (0:ℝ)) (𝓝 (1 * f 0)) := heKtend.mul hftend
      rw [one_mul, hf0] at hKtend
      exact hKtend.congr' hev.symm
    rw [show 𝓝 (0:ℝ) = 𝓝[≤] (0:ℝ) ⊔ 𝓝[>] (0:ℝ) from (nhdsLE_sup_nhdsGT (0:ℝ)).symm]
    exact hle.sup hgt
  -- Integrability of H
  have hIntH : Integrable H := by
    rw [hH, integrable_indicator_iff measurableSet_Icc]
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    exact ((by fun_prop : Continuous (fun v : ℝ => Complex.exp (-(u * (L:ℂ) * (v:ℂ)))))).continuousOn.mul hcont
  -- The Laplace bound for the inner integral
  set Cst : ℝ := 3*B*x₀/L^2 with hCst
  have hu2pos : 0 < (u.re)^2 := pow_pos hu 2
  have hbound : ∀ τ : ℝ,
      ‖∫ v in (0:ℝ)..x₀, Complex.exp (-((u - (τ:ℂ)*Complex.I)*(L:ℂ)*(v:ℂ))) * f v‖
        ≤ Cst * ((u.re)^2 + (τ - u.im)^2)⁻¹ := by
    intro τ
    have hzre : 0 < ((u - (τ:ℂ)*Complex.I) * (L:ℂ)).re := by
      have hthis : ((u - (τ:ℂ)*Complex.I) * (L:ℂ)).re = u.re * L := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [hthis]; positivity
    have h := Commons.Analysis.Integral.laplace_bound_piecewiseC2 hx₀ hcont hf2 hBnd hfx₀ hf0
      (z := (u - (τ:ℂ)*Complex.I) * (L:ℂ)) hzre
    have hznorm : ‖(u - (τ:ℂ)*Complex.I) * (L:ℂ)‖^2 = L^2 * ((u.re)^2 + (τ - u.im)^2) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hre : ((u - (τ:ℂ)*Complex.I) * (L:ℂ)).re = u.re * L := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      have him : ((u - (τ:ℂ)*Complex.I) * (L:ℂ)).im = (u.im - τ) * L := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [hre, him]; ring
    calc ‖∫ v in (0:ℝ)..x₀, Complex.exp (-((u - (τ:ℂ)*Complex.I)*(L:ℂ)*(v:ℂ))) * f v‖
        ≤ 1 / ‖(u - (τ:ℂ)*Complex.I)*(L:ℂ)‖^2 * (3*B*x₀) := h
      _ = Cst * ((u.re)^2 + (τ-u.im)^2)⁻¹ := by
          rw [hznorm, hCst]
          field_simp
  -- Integrability of the Fourier transform
  have hIntFH : Integrable (𝓕 H) := by
    have hrat : Integrable (fun y : ℝ => ((u.re)^2 + (y/c - u.im)^2)⁻¹) volume :=
      integrable_inv_sq_affine hu2pos hcne
    have hg : Integrable (fun y : ℝ => Cst * ((u.re)^2 + (y/c - u.im)^2)⁻¹) volume :=
      hrat.const_mul Cst
    refine hg.mono' ?_ ?_
    · exact (continuous_fourier hIntH).aestronglyMeasurable
    · filter_upwards with y
      have hcc : c * (y / c) = y := by field_simp
      have h1 : 𝓕 H y = F (y / c) := by
        have h2 : 𝓕 H y = 𝓕 H (c * (y / c)) := by rw [hcc]
        rw [h2, ← hFid (y / c)]
      rw [h1]
      exact hbound (y/c)
  -- Assembly
  change (∫ t : ℝ, F t) = 0
  have hsub : (∫ t : ℝ, F t) = |c⁻¹| • (∫ y : ℝ, 𝓕 H y) := by
    have hfe : (fun t : ℝ => F t) = fun t => 𝓕 H (c * t) := funext hFid
    rw [hfe, Measure.integral_comp_mul_left]
  have hInv : (∫ y : ℝ, 𝓕 H y) = H 0 := by
    have h := MeasureTheory.Integrable.fourierInv_fourier_eq hIntH hIntFH hHcont0
    rw [Real.fourierInv_eq] at h
    simpa using h
  rw [hsub, hInv, hH0, smul_zero]

end Commons.Analysis.Fourier