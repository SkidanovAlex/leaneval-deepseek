import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Commons.Analysis.Fourier.exists_invFourier_compact_pos

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform Filter
open scoped FourierTransform RealInnerProductSpace Convolution ComplexConjugate

set_option autoImplicit false

/-- Double Fourier transform of a Schwartz function is the reflection of the function. -/
lemma schwartz_fourier_fourier_coe {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ) :
    ⇑(𝓕 (𝓕 f) : SchwartzMap V ℂ) = fun x => ⇑f (-x) := by
  funext x
  have h2 : (𝓕⁻ (𝓕 (⇑f)) : V → ℂ) = ⇑f :=
    Continuous.fourierInv_fourier_eq f.continuous f.integrable
      (𝓕 f : SchwartzMap V ℂ).integrable
  have hx := congr_fun h2 (-x)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at hx
  change 𝓕 (𝓕 (⇑f)) x = ⇑f (-x)
  exact hx

/-- The Fourier transform is homogeneous under scalar multiplication of complex-valued functions. -/
lemma real_fourier_const_smul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (c : ℂ) (f : V → ℂ) :
    𝓕 (fun x => c • f x) = fun ξ => c • 𝓕 f ξ := by
  funext ξ
  rw [Real.fourier_eq, Real.fourier_eq]
  rw [show (fun v => 𝐞 (-inner ℝ v ξ) • (c • f v))
        = (fun v => c • (𝐞 (-inner ℝ v ξ) • f v)) from by funext v; rw [smul_comm]]
  rw [integral_smul]

theorem exists_schwartz_nonneg_compactSupport_fourier (d : ℕ) :
    ∃ φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ,
      (∀ x, (φ x).im = 0) ∧ (∀ x, 0 ≤ (φ x).re) ∧
      HasCompactSupport
        (FourierTransform.fourier (fun x : EuclideanSpace ℝ (Fin d) => φ x)) ∧
      (∫ x, φ x) = 1 := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let bump : ContDiffBump (0 : E) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let b : E → ℝ := bump.normed volume
  have hb_smooth : ContDiff ℝ (⊤ : ℕ∞) b := bump.contDiff_normed
  have hb_cs : HasCompactSupport b := bump.hasCompactSupport_normed
  have hb_nn : ∀ x, 0 ≤ b x := fun x => bump.nonneg_normed x
  have hb_int : Integrable b volume := bump.integrable_normed
  have hbintval : ∫ x, b x = 1 := bump.integral_normed
  let w : E → ℝ := fun t => (b t) ^ 2
  have hb_cs' : HasCompactSupport (fun x : E => (b x : ℂ)) := hb_cs.mono (by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [h]))
  have hb_smooth' : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => (b x : ℂ)) :=
    (Complex.ofRealCLM.contDiff).comp hb_smooth
  let χ : SchwartzMap E ℂ := HasCompactSupport.toSchwartzMap hb_cs' hb_smooth'
  have hχ_coe : ⇑χ = fun x : E => (b x : ℂ) :=
    funext (fun x => HasCompactSupport.toSchwartzMap_toFun hb_cs' hb_smooth' x)
  have hχ_real : ∀ x, (χ x).im = 0 := by intro x; rw [hχ_coe]; simp
  have hχ_cs : HasCompactSupport (⇑χ) := by rw [hχ_coe]; exact hb_cs'
  let χn : SchwartzMap E ℂ := HasCompactSupport.toSchwartzMap
      (hb_cs'.comp_homeomorph (Homeomorph.neg E)) (hb_smooth'.comp contDiff_neg)
  have hχn_coe : ⇑χn = fun x : E => (b (-x) : ℂ) :=
    funext (fun x => HasCompactSupport.toSchwartzMap_toFun _ _ x)
  have hχn_cs : HasCompactSupport (⇑χn) := by
    rw [hχn_coe]; exact hb_cs'.comp_homeomorph (Homeomorph.neg E)
  have hχn_eq : ⇑χn = fun x => ⇑χ (-x) := by rw [hχn_coe, hχ_coe]
  have hFχ0 : 𝓕 (⇑χ) 0 = 1 := by
    have hf : 𝓕 (⇑χ) 0 = ∫ v, ⇑χ v := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards with v
      simp [Circle.smul_def, Real.fourierChar_apply]
    rw [hf, hχ_coe, integral_complex_ofReal, hbintval, Complex.ofReal_one]
  let B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ
  let ψ : SchwartzMap E ℂ := SchwartzMap.convolution B χ χn
  let φ₀ : SchwartzMap E ℂ := 𝓕 ψ
  have hψ_coe : ⇑ψ = MeasureTheory.convolution (⇑χ) (⇑χn) B volume :=
    funext (fun x => SchwartzMap.convolution_apply B χ χn x)
  have hψ_cs : HasCompactSupport (⇑ψ) := by
    rw [hψ_coe]; exact hχ_cs.convolution B hχn_cs
  have hφ₀_val : ∀ ξ, ⇑φ₀ ξ = ((‖𝓕 (⇑χ) ξ‖ ^ 2 : ℝ) : ℂ) := by
    intro ξ
    have hcoe : ⇑φ₀ = 𝓕 (⇑ψ) := by
      change ⇑(𝓕 ψ : SchwartzMap E ℂ) = 𝓕 (⇑ψ)
      exact SchwartzMap.fourier_coe ψ
    rw [hcoe, hψ_coe]
    rw [Real.fourier_bilin_convolution_eq B χ.integrable χn.integrable ξ]
    have hconj : 𝓕 (⇑χn) ξ = conj (𝓕 (⇑χ) ξ) := by
      rw [hχn_eq]
      exact fourier_comp_neg_eq_conj hχ_real ξ
    rw [hconj]
    change (𝓕 (⇑χ) ξ) * conj (𝓕 (⇑χ) ξ) = ((‖𝓕 (⇑χ) ξ‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.mul_conj']
    push_cast
    ring
  -- evaluation of ψ at 0
  have hpt : ∀ t : E, B (⇑χ t) (⇑χn (0 - t)) = ((w t : ℝ) : ℂ) := by
    intro t
    rw [hχ_coe, hχn_coe]
    rw [show (0 : E) - t = -t from zero_sub t]
    change ContinuousLinearMap.mul ℂ ℂ (↑(b t)) (↑(b (-(-t)))) = ((w t : ℝ) : ℂ)
    rw [neg_neg]
    change (↑(b t) : ℂ) * (↑(b t)) = ((w t : ℝ) : ℂ)
    rw [show w t = (b t) ^ 2 from rfl]
    push_cast
    ring
  have hψ0 : ⇑ψ 0 = ((∫ t, w t : ℝ) : ℂ) := by
    rw [hψ_coe]
    have hconv : MeasureTheory.convolution (⇑χ) (⇑χn) B volume 0
        = ∫ t, B (⇑χ t) (⇑χn (0 - t)) := rfl
    rw [hconv]
    have hint : (∫ t, B (⇑χ t) (⇑χn (0 - t))) = ∫ t, ((w t : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with t
      exact hpt t
    rw [hint, integral_complex_ofReal]
  -- integral of φ₀ equals ψ 0
  have hIntφ₀ : ∫ x, ⇑φ₀ x = ((∫ t, w t : ℝ) : ℂ) := by
    have h1 : (∫ x, ⇑φ₀ x) = 𝓕⁻ (⇑φ₀) 0 := by
      rw [Real.fourierInv_eq]
      apply integral_congr_ae
      filter_upwards with v
      simp [Circle.smul_def, Real.fourierChar_apply]
    rw [h1]
    have h2 : (𝓕⁻ (⇑φ₀) : E → ℂ) = ⇑ψ := by
      rw [← SchwartzMap.fourierInv_coe φ₀]
      rw [show φ₀ = 𝓕 ψ from rfl, FourierTransform.fourierInv_fourier_eq ψ]
    rw [h2, hψ0]
  -- positivity of A
  let A : ℝ := ∫ t, w t
  have hw_cont : Continuous w := by
    show Continuous (fun t : E => (b t) ^ 2)
    exact hb_smooth.continuous.pow 2
  have hw_cs : HasCompactSupport w := hb_cs.mono (by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h
    exact hx (by rw [show w x = (b x)^2 from rfl, h]; ring))
  have hw_int : Integrable w volume := hw_cont.integrable_of_hasCompactSupport hw_cs
  have hw_supp : Function.support w = Function.support b := by
    ext x
    simp only [Function.mem_support, ne_eq]
    show (b x) ^ 2 ≠ 0 ↔ b x ≠ 0
    constructor
    · intro h hb; exact h (by rw [hb]; ring)
    · intro h hb; exact h (sq_eq_zero_iff.mp hb)
  have hb_supp_pos : 0 < volume (Function.support b) :=
    (integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hb_nn) hb_int).mp
      (by rw [hbintval]; norm_num)
  have hApos : 0 < A := by
    have : 0 < ∫ t, w t := by
      rw [integral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall (fun t => sq_nonneg (b t))) hw_int, hw_supp]
      exact hb_supp_pos
    exact this
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hIntφ₀A : ∫ x, ⇑φ₀ x = ((A : ℝ) : ℂ) := hIntφ₀
  -- the final function
  let φ : SchwartzMap E ℂ := (((A⁻¹ : ℝ) : ℂ)) • φ₀
  have hφx : ∀ x, φ x = (((A⁻¹) * (‖𝓕 (⇑χ) x‖ ^ 2) : ℝ) : ℂ) := by
    intro x
    change (((A⁻¹ : ℝ) : ℂ)) • (φ₀ x) = _
    rw [hφ₀_val x, Complex.ofReal_mul, smul_eq_mul]
  have h1 : ∀ x, (φ x).im = 0 := by intro x; rw [hφx x]; exact Complex.ofReal_im _
  have h2 : ∀ x, 0 ≤ (φ x).re := by
    intro x; rw [hφx x, Complex.ofReal_re]
    exact mul_nonneg (inv_nonneg.mpr hApos.le) (sq_nonneg _)
  have h3 : HasCompactSupport (𝓕 (fun x : E => φ x)) := by
    have hFφ₀ : (𝓕 (⇑φ₀) : E → ℂ) = fun x => ⇑ψ (-x) := by
      rw [← SchwartzMap.fourier_coe φ₀]
      exact schwartz_fourier_fourier_coe ψ
    have hfun : (fun x : E => φ x) = fun x => ((A⁻¹ : ℝ) : ℂ) • (⇑φ₀ x) := by
      funext x
      change φ x = ((A⁻¹ : ℝ) : ℂ) • (φ₀ x)
      rfl
    rw [hfun, real_fourier_const_smul, hFφ₀]
    have hcs : HasCompactSupport (fun x : E => ⇑ψ (-x)) :=
      hψ_cs.comp_homeomorph (Homeomorph.neg E)
    exact HasCompactSupport.smul_left (f := fun _ : E => ((A⁻¹ : ℝ) : ℂ)) hcs
  have h4 : (∫ x, φ x) = 1 := by
    have hfun : (fun x : E => φ x) = fun x => ((A⁻¹ : ℝ) : ℂ) • (⇑φ₀ x) := by
      funext x
      change φ x = ((A⁻¹ : ℝ) : ℂ) • (φ₀ x)
      rfl
    rw [hfun, integral_smul, hIntφ₀A, smul_eq_mul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hAne, Complex.ofReal_one]
  exact ⟨φ, h1, h2, h3, h4⟩

end Commons.Analysis.Fourier
