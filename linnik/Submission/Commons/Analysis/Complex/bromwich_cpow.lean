import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Submission.Commons.Analysis.Complex.gamma_integral_cpow
import Submission.Commons.Analysis.Complex.laplace_inversion_smooth

namespace Commons.Analysis.Complex

open MeasureTheory Set
open scoped FourierTransform

/-- Two-sided Laplace inversion in the "+ form": the Bromwich integral of the
Laplace transform `s ↦ ∫ t, e^{s t} f t` with a factor `e^{-s u}` recovers `f u`. -/
theorem laplace_inversion_smooth_pos {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcpt : HasCompactSupport f) (c : ℝ) (hc : c ≠ 0) (u : ℝ) :
    f u = (1 / (2 * Real.pi)) * ∫ γ : ℝ,
      (∫ t : ℝ, Complex.exp ((((c : ℂ) + γ * Complex.I)) * (t : ℂ)) * f t)
        * Complex.exp (-(((c : ℂ) + γ * Complex.I)) * (u : ℂ)) := by
  set F : ℝ → ℂ := fun t => f (-t) with hFdef
  have hFdiff : ContDiff ℝ (⊤ : ℕ∞) F := by
    rw [hFdef]; exact hf.comp contDiff_neg
  have hFcpt : HasCompactSupport F := by
    rw [hFdef]
    exact hcpt.comp_homeomorph (Homeomorph.neg ℝ)
  have h := laplace_inversion_smooth hFdiff hFcpt c (-u) hc
  rw [hFdef] at h
  simp only [neg_neg] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards with γ
  have hinner : (∫ t : ℝ, Complex.exp (-(((c:ℂ)+γ*Complex.I)*(t:ℂ))) * f (-t))
      = ∫ t : ℝ, Complex.exp ((((c:ℂ)+γ*Complex.I))*(t:ℂ)) * f t := by
    rw [← MeasureTheory.integral_neg_eq_self
        (fun x : ℝ => Complex.exp ((((c:ℂ)+γ*Complex.I))*(x:ℂ)) * f x) volume]
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    push_cast
    ring
  have hexp : Complex.exp ((((c:ℂ)+γ*Complex.I))*(((-u:ℝ):ℂ)))
      = Complex.exp (-(((c:ℂ)+γ*Complex.I))*((u:ℝ):ℂ)) := by
    congr 1; push_cast; ring
  rw [hinner, hexp]

/-- Integrability of the two-sided Laplace transform `τ ↦ ∫ t, e^{(c+iτ)t} f t`. -/
theorem integrable_laplace_kernel {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcpt : HasCompactSupport f) (c : ℝ) :
    Integrable (fun τ : ℝ => ∫ t : ℝ, Complex.exp ((((c : ℂ) + τ * Complex.I)) * (t : ℂ)) * f t) volume := by
  set h : ℝ → ℂ := fun t => Complex.exp ((c:ℂ)*(t:ℂ)) * f t with hh
  have hsm : ContDiff ℝ (⊤ : ℕ∞) h := by
    rw [hh]
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t:ℂ)) := by
      convert Complex.ofRealCLM.contDiff using 1
      ext t; simp [Complex.ofRealCLM_apply]
    exact (((contDiff_const.mul hlin)).cexp).mul hf
  have hcpt' : HasCompactSupport h := by
    rw [hh]; exact hcpt.mul_left
  have hFS : Integrable (𝓕 h) volume := by
    let S : SchwartzMap ℝ ℂ := hcpt'.toSchwartzMap hsm
    have h2 : Integrable (⇑(𝓕 S : SchwartzMap ℝ ℂ)) volume := (𝓕 S : SchwartzMap ℝ ℂ).integrable
    rw [SchwartzMap.fourier_coe] at h2
    exact h2
  have hG_eq : ∀ τ : ℝ, (∫ t : ℝ, Complex.exp ((((c:ℂ)+τ*Complex.I))*(t:ℂ)) * f t)
      = 𝓕 h (-τ / (2 * Real.pi)) := by
    intro τ
    rw [Real.fourier_eq', hh]
    apply integral_congr_ae
    filter_upwards with t
    simp only [Real.inner_apply, smul_eq_mul]
    rw [show Complex.exp (↑(-2 * Real.pi * (t * (-τ / (2 * Real.pi))) : ℝ) * Complex.I)
              * (Complex.exp (↑c * ↑t) * f t)
            = Complex.exp ((↑(-2 * Real.pi * (t * (-τ / (2 * Real.pi))) : ℝ) * Complex.I)
                + (↑c * ↑t)) * f t by
          rw [← mul_assoc, ← Complex.exp_add]]
    congr 1
    push_cast
    field_simp
    ring
  have h1 : Integrable (fun τ : ℝ => 𝓕 h (-1 / (2*Real.pi) * τ)) volume :=
    hFS.comp_mul_left' (by positivity)
  have h2 : Integrable (fun τ : ℝ => 𝓕 h (-τ / (2*Real.pi))) volume :=
    h1.congr (Filter.Eventually.of_forall (fun τ => by ring_nf))
  exact h2.congr (Filter.Eventually.of_forall (fun τ => (hG_eq τ).symm))

/-- Continuity of the two-sided Laplace transform `τ ↦ ∫ t, e^{(c+iτ)t} f t`. -/
theorem continuous_laplace_kernel {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcpt : HasCompactSupport f) (c : ℝ) :
    Continuous (fun τ : ℝ => ∫ t : ℝ, Complex.exp ((((c : ℂ) + τ * Complex.I)) * (t : ℂ)) * f t) := by
  set h : ℝ → ℂ := fun t => Complex.exp ((c:ℂ)*(t:ℂ)) * f t with hh
  have hsm : ContDiff ℝ (⊤ : ℕ∞) h := by
    rw [hh]
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t:ℂ)) := by
      convert Complex.ofRealCLM.contDiff using 1
      ext t; simp [Complex.ofRealCLM_apply]
    exact (((contDiff_const.mul hlin)).cexp).mul hf
  have hcpt' : HasCompactSupport h := by
    rw [hh]; exact hcpt.mul_left
  have hcont_fourier : Continuous (𝓕 h) := by
    let S : SchwartzMap ℝ ℂ := hcpt'.toSchwartzMap hsm
    have h2 : Continuous (⇑(𝓕 S : SchwartzMap ℝ ℂ)) := (𝓕 S : SchwartzMap ℝ ℂ).continuous
    rwa [SchwartzMap.fourier_coe] at h2
  have hG_eq : ∀ τ : ℝ, (∫ t : ℝ, Complex.exp ((((c:ℂ)+τ*Complex.I))*(t:ℂ)) * f t)
      = 𝓕 h (-τ / (2 * Real.pi)) := by
    intro τ
    rw [Real.fourier_eq', hh]
    apply integral_congr_ae
    filter_upwards with t
    simp only [Real.inner_apply, smul_eq_mul]
    rw [show Complex.exp (↑(-2 * Real.pi * (t * (-τ / (2 * Real.pi))) : ℝ) * Complex.I)
              * (Complex.exp (↑c * ↑t) * f t)
            = Complex.exp ((↑(-2 * Real.pi * (t * (-τ / (2 * Real.pi))) : ℝ) * Complex.I)
                + (↑c * ↑t)) * f t by
          rw [← mul_assoc, ← Complex.exp_add]]
    congr 1
    push_cast
    field_simp
    ring
  have hc : Continuous (fun τ : ℝ => 𝓕 h (-τ / (2*Real.pi))) :=
    hcont_fourier.comp (by continuity)
  exact hc.congr (fun τ => (hG_eq τ).symm)

/-- Norm of the Bromwich kernel factor on the half-line `u > 0`. -/
theorem norm_kernel_factor (c α τ u : ℝ) (hu : 0 < u) :
    ‖((u:ℂ)) ^ ((α:ℂ) - 1) * Complex.exp (-((((c:ℂ) + τ*Complex.I)) * (u:ℂ)))‖
      = u ^ (α - 1) * Real.exp (-(c*u)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp]
  have hre : (-(((c:ℂ)+τ*Complex.I)*(u:ℂ))).re = -(c*u) := by
    simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [hre]
  congr 1

theorem bromwich_cpow (c : ℝ) (hc : 0 < c) (α : ℝ) (hα : 0 < α) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcpt : HasCompactSupport f) :
    (1 / (2 * Real.pi)) * ∫ τ : ℝ, (((c : ℂ) + τ * Complex.I)) ^ (-(α : ℂ))
        * (∫ t : ℝ, Complex.exp ((((c : ℂ) + τ * Complex.I)) * (t : ℂ)) * f t)
      = (1 / Complex.Gamma (α : ℂ)) *
          ∫ t : ℝ in Set.Ioi 0, ((t : ℂ)) ^ ((α : ℂ) - 1) * f t := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hΓ : Complex.Gamma (α:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hα)
  let s : ℝ → ℂ := fun τ => (c : ℂ) + τ * Complex.I
  let G : ℝ → ℂ := fun τ => ∫ t : ℝ, Complex.exp ((s τ) * (t : ℂ)) * f t
  let K : ℝ → ℝ → ℂ := fun τ u => (u : ℂ) ^ ((α : ℂ) - 1) * Complex.exp (-(s τ * (u : ℂ)))
  let φ : ℝ → ℝ := (Set.Ioi 0).indicator (fun u => u ^ (α - 1) * Real.exp (-(c*u)))
  change (1 / (2 * Real.pi)) * ∫ τ : ℝ, (s τ) ^ (-(α : ℂ)) * G τ
      = (1 / Complex.Gamma (α : ℂ)) * ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ ((α : ℂ) - 1) * f t
  have hGint : Integrable G volume := integrable_laplace_kernel hf hcpt c
  have hGcont : Continuous G := continuous_laplace_kernel hf hcpt c
  have hrep : ∀ τ : ℝ, (s τ) ^ (-(α:ℂ))
      = (1 / Complex.Gamma (α:ℂ)) * ∫ u : ℝ in Set.Ioi 0, K τ u := by
    intro τ
    have h := gamma_integral_cpow (a := (α:ℂ)) (z := (c:ℂ) + τ*Complex.I)
        (by simpa using hα) (by simpa using hc)
    rw [h, one_div, ← mul_assoc, inv_mul_cancel₀ hΓ, one_mul]
  have hφint : Integrable φ volume := by
    rw [show φ = (Set.Ioi 0).indicator (fun u : ℝ => u ^ (α - 1) * Real.exp (-(c*u))) from rfl,
        integrable_indicator_iff measurableSet_Ioi]
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := α - 1) (p := 1) (b := c)
      (by linarith) (by norm_num) hc
    simpa using h
  have hFint : Integrable (fun p : ℝ × ℝ => K p.1 p.2 * G p.1)
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
    have hGnorm : Integrable (fun τ : ℝ => ‖G τ‖) volume := hGint.norm
    have hdom : Integrable (fun p : ℝ × ℝ => φ p.2 * ‖G p.1‖)
        (volume.prod (volume.restrict (Set.Ioi 0))) := by
      have h := hGnorm.mul_prod (hφint.integrableOn (s := Set.Ioi 0))
      exact h.congr (Filter.Eventually.of_forall (fun p => by ring))
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => K p.1 p.2 * G p.1)
        (volume.prod (volume.restrict (Set.Ioi 0))) := by
      have hconv : (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))
          = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
        rw [← Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
              (Set.univ) (Set.Ioi 0)]
        simp
      rw [hconv]
      apply ContinuousOn.aestronglyMeasurable _ (MeasurableSet.univ.prod measurableSet_Ioi)
      have hA : ContinuousOn (fun p : ℝ × ℝ => (p.2:ℂ)^((α:ℂ)-1)) (Set.univ ×ˢ Set.Ioi 0) := by
        apply ContinuousOn.cpow_const
        · exact (Complex.continuous_ofReal.comp continuous_snd).continuousOn
        · intro p hp
          rw [Complex.slitPlane_eq_union]
          left
          simpa using hp.2
      have hB : ContinuousOn (fun p : ℝ × ℝ => Complex.exp (-(s p.1 * (p.2:ℂ))))
          (Set.univ ×ˢ Set.Ioi 0) := by
        apply ContinuousOn.cexp
        simp only [s]
        fun_prop
      have hC : ContinuousOn (fun p : ℝ × ℝ => G p.1) (Set.univ ×ˢ Set.Ioi 0) :=
        (hGcont.comp continuous_fst).continuousOn
      have hh := (hA.mul hB).mul hC
      convert hh using 1
      all_goals (ext p; simp only [K, Pi.mul_apply])
    refine Integrable.mono hdom hmeas ?_
    have hmem : ∀ᵐ p ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))),
        p.2 ∈ Set.Ioi 0 := by
      rw [Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_snd)]
      filter_upwards with τ
      exact ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with p hp
    have hk : ‖K p.1 p.2‖ = p.2^(α-1)*Real.exp (-(c*p.2)) := by
      simp only [K]
      exact norm_kernel_factor c α p.1 p.2 hp
    have hφp : φ p.2 = p.2^(α-1)*Real.exp (-(c*p.2)) := by
      simp only [φ, Set.indicator_of_mem hp]
    rw [norm_mul, hk, hφp]
    have hnn : 0 ≤ p.2^(α-1)*Real.exp (-(c*p.2)) :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt hp) _) (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn (norm_nonneg _))]
  have h1 : (∫ τ : ℝ, (s τ) ^ (-(α:ℂ)) * G τ)
      = (1 / Complex.Gamma (α:ℂ)) * ∫ τ : ℝ, ∫ u : ℝ in Set.Ioi 0, K τ u * G τ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with τ
    rw [hrep τ, integral_mul_const]
    ring
  have h2πne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h2πC : (2:ℂ) * (Real.pi:ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hFub : (∫ τ : ℝ, ∫ u : ℝ in Set.Ioi 0, K τ u * G τ)
      = ∫ u : ℝ in Set.Ioi 0, ∫ τ : ℝ, K τ u * G τ :=
    integral_integral_swap (f := fun τ u => K τ u * G τ) hFint
  have hlapexp : ∀ u : ℝ, (∫ τ : ℝ, Complex.exp (-(s τ * (u:ℂ))) * G τ)
      = 2 * Real.pi * f u := by
    intro u
    have h := laplace_inversion_smooth_pos hf hcpt c hcne u
    have hinner_eq : (∫ γ : ℝ, (∫ t : ℝ, Complex.exp ((((c:ℂ)+γ*Complex.I))*(t:ℂ))*f t)
          * Complex.exp (-(((c:ℂ)+γ*Complex.I))*(u:ℂ)))
        = ∫ τ : ℝ, Complex.exp (-(s τ * (u:ℂ))) * G τ := by
      apply integral_congr_ae
      filter_upwards with γ
      simp only [s, G]
      have hexp : Complex.exp (-(↑c + ↑γ * Complex.I) * ↑u)
          = Complex.exp (-((↑c + ↑γ * Complex.I) * ↑u)) := by congr 1; ring
      rw [hexp, mul_comm]
    rw [hinner_eq] at h
    have hmain : ((2:ℂ)*(Real.pi:ℂ)) * f u
        = ∫ τ : ℝ, Complex.exp (-(s τ * (u:ℂ))) * G τ := by
      rw [h, ← mul_assoc, one_div, mul_inv_cancel₀ h2πC, one_mul]
    rw [hmain]
  have hinner : ∀ u : ℝ, (∫ τ : ℝ, K τ u * G τ)
      = (u:ℂ) ^ ((α:ℂ) - 1) * (∫ τ : ℝ, Complex.exp (-(s τ * (u:ℂ))) * G τ) := by
    intro u
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with τ
    simp only [K]
    ring
  have hU : (∫ u : ℝ in Set.Ioi 0, ∫ τ : ℝ, K τ u * G τ)
      = ∫ u : ℝ in Set.Ioi 0, (2 * Real.pi) * ((u:ℂ)^((α:ℂ)-1) * f u) := by
    apply integral_congr_ae
    filter_upwards with u
    rw [hinner u, hlapexp u]
    ring
  rw [h1, hFub, hU, integral_const_mul]
  field_simp

end Commons.Analysis.Complex