import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open MeasureTheory Real Complex
open scoped FourierTransform

namespace Commons.Analysis.Fourier

private noncomputable def poleX (ξ : ℝ) : ℂ := 1 - 2 * Real.pi * Complex.I * ξ

private lemma poleX_re (ξ : ℝ) : (poleX ξ).re = 1 := by simp [poleX]

private lemma poleX_add (ξ ξ' : ℝ) : poleX ξ + poleX ξ' = 2 - 2 * Real.pi * Complex.I * (ξ + ξ') := by
  simp [poleX]; ring

private lemma poleKernel_eq (ξ ξ' : ℝ) :
    ((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ')) /
      (2 - 2 * Real.pi * Complex.I * (ξ + ξ'))
    = poleX ξ * poleX ξ' / (poleX ξ + poleX ξ') := by
  rw [← poleX_add ξ ξ']
  simp [poleX]

private lemma poleKernel (ξ ξ' : ℝ) :
    (poleX ξ * poleX ξ' / (poleX ξ + poleX ξ')) =
      ∫ t : ℝ in Set.Ioi 0,
        (poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ)) *
          (poleX ξ' * Complex.exp (-(t:ℂ) * poleX ξ')) := by
  set z : ℂ := poleX ξ + poleX ξ' with hz
  have hzre : z.re = 2 := by
    rw [hz, Complex.add_re, poleX_re, poleX_re]; norm_num
  have hzlt : (-z).re < 0 := by rw [Complex.neg_re, hzre]; norm_num
  have hz0 : z ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hzre] at this; norm_num at this
  have h := integral_exp_mul_complex_Ioi (a := -z) hzlt 0
  have h' : (∫ x : ℝ in Set.Ioi 0, cexp ((-z) * (x:ℂ))) = 1/z := by
    rw [h]; simp
  have hInt : (∫ t : ℝ in Set.Ioi 0,
        (poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ)) *
          (poleX ξ' * Complex.exp (-(t:ℂ) * poleX ξ')))
      = (poleX ξ * poleX ξ') * (∫ t : ℝ in Set.Ioi 0, cexp ((-z) * (t:ℂ))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    have hE : cexp (-(t:ℂ) * poleX ξ) * cexp (-(t:ℂ) * poleX ξ') = cexp ((-z) * (t:ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hz]; ring
    calc poleX ξ * cexp (-(t:ℂ) * poleX ξ) * (poleX ξ' * cexp (-(t:ℂ) * poleX ξ'))
        = (poleX ξ * poleX ξ') * (cexp (-(t:ℂ) * poleX ξ) * cexp (-(t:ℂ) * poleX ξ')) := by ring
      _ = (poleX ξ * poleX ξ') * cexp ((-z) * (t:ℂ)) := by rw [hE]
  rw [hInt, h', hz]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

private lemma poleX_mul_fourier (A : SchwartzMap ℝ ℂ) :
    (fun ξ : ℝ => poleX ξ * (SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) A) ξ)
      = (SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) (A - LineDeriv.lineDerivOp (1:ℝ) A) : ℝ → ℂ) := by
  rw [show SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) (A - LineDeriv.lineDerivOp (1:ℝ) A)
      = SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) A - SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) (LineDeriv.lineDerivOp (1:ℝ) A) from map_sub _ _ _]
  simp only [SchwartzMap.fourierTransformCLM_apply]
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  ext ξ
  simp only [sub_apply, smul_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp only [RCLike.inner_apply, ringHom_apply, one_mul, smul_eq_mul, poleX]
  rw [Complex.real_smul]
  ring

private lemma integrable_poleX_mul_fourier (A : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => poleX ξ * (SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) A) ξ) volume := by
  rw [poleX_mul_fourier]
  exact (SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) (A - LineDeriv.lineDerivOp (1:ℝ) A)).integrable

private lemma keyLaplace (A : SchwartzMap ℝ ℂ) (t : ℝ) :
    ∫ ξ : ℝ, poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ) *
        (SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) A) ξ
      = Complex.exp (-(t:ℂ)) * (A t - deriv (⇑A) t) := by
  set gA := SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) A with hgA
  have hfun : (fun ξ : ℝ => poleX ξ * gA ξ)
      = (SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) (A - LineDeriv.lineDerivOp (1:ℝ) A) : ℝ → ℂ) := by
    rw [hgA]; exact poleX_mul_fourier A
  have hcexp : ∀ ξ : ℝ, Complex.exp (-(t:ℂ) * poleX ξ)
      = Complex.exp (-(t:ℂ)) * ↑(𝐞 (ξ*t)) := by
    intro ξ
    simp only [poleX]
    rw [fourierChar_apply, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h1 : (∫ ξ : ℝ, poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ) * gA ξ)
      = Complex.exp (-(t:ℂ)) * ∫ ξ : ℝ, 𝐞 (ξ*t) • (poleX ξ * gA ξ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hcexp ξ, Circle.smul_def, smul_eq_mul]
    ring
  have hcoef : (𝓕⁻ (fun ξ : ℝ => poleX ξ * gA ξ)) t
      = (A - LineDeriv.lineDerivOp (1:ℝ) A) t := by
    have hcont : Continuous (⇑(A - LineDeriv.lineDerivOp (1:ℝ) A)) :=
      (A - LineDeriv.lineDerivOp (1:ℝ) A).continuous
    have hint : Integrable (⇑(A - LineDeriv.lineDerivOp (1:ℝ) A)) :=
      (A - LineDeriv.lineDerivOp (1:ℝ) A).integrable
    have hft : Integrable (𝓕 (⇑(A - LineDeriv.lineDerivOp (1:ℝ) A))) volume := by
      rw [← SchwartzMap.fourier_coe (A - LineDeriv.lineDerivOp (1:ℝ) A)]
      exact (SchwartzMap.fourierTransformCLM ℂ (V:=ℝ) (A - LineDeriv.lineDerivOp (1:ℝ) A)).integrable
    have hinv := congrFun (Continuous.fourierInv_fourier_eq hcont hint hft) t
    rw [← SchwartzMap.fourier_coe (A - LineDeriv.lineDerivOp (1:ℝ) A)] at hinv
    rw [← SchwartzMap.fourierTransformCLM_apply ℂ] at hinv
    rw [← hfun] at hinv
    exact hinv
  have h2 : (∫ ξ : ℝ, 𝐞 (ξ*t) • (poleX ξ * gA ξ))
      = (A - LineDeriv.lineDerivOp (1:ℝ) A) t := by
    rw [show (∫ ξ : ℝ, 𝐞 (ξ*t) • (poleX ξ * gA ξ))
        = (𝓕⁻ (fun ξ : ℝ => poleX ξ * gA ξ)) t from ?_]
    · rw [hcoef]
    · rw [fourierInv_eq]
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [inner_apply]
  rw [h1, h2]
  simp only [sub_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl



private lemma norm_poleX_cexp_mul (g : SchwartzMap ℝ ℂ) (t ξ : ℝ) :
    ‖poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ) * g ξ‖ = ‖poleX ξ * g ξ‖ * Real.exp (-t) := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp]
  have : (-(t:ℂ) * poleX ξ).re = -t := by
    simp [Complex.mul_re, poleX_re]
  rw [this]; ring

theorem fourier_pole_identity (A B : SchwartzMap ℝ ℂ) :
    ∫ ξ : ℝ, ∫ ξ' : ℝ,
        ((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ')) /
          (2 - 2 * Real.pi * Complex.I * (ξ + ξ')) *
            (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) A) ξ *
            (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) B) ξ'
      = ∫ t : ℝ in Set.Ioi 0,
          (Complex.exp (-t) * (deriv (⇑A) t - A t)) *
            (Complex.exp (-t) * (deriv (⇑B) t - B t)) := by
  set gA := SchwartzMap.fourierTransformCLM ℂ (V := ℝ) A with hgA
  set gB := SchwartzMap.fourierTransformCLM ℂ (V := ℝ) B with hgB
  have hker : ∀ ξ ξ' : ℝ,
      ((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ')) /
          (2 - 2 * Real.pi * Complex.I * (ξ + ξ')) * gA ξ * gB ξ'
        = ∫ t : ℝ in Set.Ioi 0,
            (poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ) * gA ξ) *
              (poleX ξ' * Complex.exp (-(t:ℂ) * poleX ξ') * gB ξ') := by
    intro ξ ξ'
    rw [poleKernel_eq ξ ξ']
    have hk := poleKernel ξ ξ'
    calc (poleX ξ * poleX ξ' / (poleX ξ + poleX ξ')) * gA ξ * gB ξ'
        = (poleX ξ * poleX ξ' / (poleX ξ + poleX ξ')) * (gA ξ * gB ξ') := by ring
      _ = (∫ t : ℝ in Set.Ioi 0, (poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ)) *
              (poleX ξ' * Complex.exp (-(t:ℂ) * poleX ξ'))) * (gA ξ * gB ξ') := by rw [hk]
      _ = ∫ t : ℝ in Set.Ioi 0, (poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ) * gA ξ) *
              (poleX ξ' * Complex.exp (-(t:ℂ) * poleX ξ') * gB ξ') := by
          rw [← integral_mul_const]
          apply integral_congr_ae
          filter_upwards with t
          ring
  let Φ : (ℝ × ℝ) × ℝ → ℂ := fun z =>
      (poleX z.1.1 * Complex.exp (-(z.2:ℂ) * poleX z.1.1) * gA z.1.1) *
        (poleX z.1.2 * Complex.exp (-(z.2:ℂ) * poleX z.1.2) * gB z.1.2)
  have huA : Integrable (fun ξ : ℝ => poleX ξ * gA ξ) volume := by
    rw [hgA]; exact integrable_poleX_mul_fourier A
  have huB : Integrable (fun ξ : ℝ => poleX ξ * gB ξ) volume := by
    rw [hgB]; exact integrable_poleX_mul_fourier B
  have hAn : Integrable (fun ξ : ℝ => ‖poleX ξ * gA ξ‖) volume := huA.norm
  have hBn : Integrable (fun ξ : ℝ => ‖poleX ξ * gB ξ‖) volume := huB.norm
  have hprod : Integrable (fun p : ℝ × ℝ => ‖poleX p.1 * gA p.1‖ * ‖poleX p.2 * gB p.2‖)
      (volume.prod volume) := hAn.mul_prod hBn
  have hexp : Integrable (fun t : ℝ => Real.exp (-2 * t)) (volume.restrict (Set.Ioi 0)) := by
    have := integrableOn_exp_mul_Ioi (a := -2) (by norm_num) 0
    simpa [IntegrableOn] using this
  have hPsi : Integrable (fun z : (ℝ × ℝ) × ℝ =>
      ‖poleX z.1.1 * gA z.1.1‖ * ‖poleX z.1.2 * gB z.1.2‖ * Real.exp (-2 * z.2))
      ((volume.prod volume).prod (volume.restrict (Set.Ioi 0))) := by
    have := hprod.mul_prod hexp
    simpa using this
  have hmeasPhi : AEStronglyMeasurable Φ ((volume.prod volume).prod (volume.restrict (Set.Ioi 0))) := by
    apply Continuous.aestronglyMeasurable
    simp only [Φ, poleX]
    fun_prop
  have hboundPhi : ∀ᵐ z ∂((volume.prod volume).prod (volume.restrict (Set.Ioi 0))),
      ‖Φ z‖ ≤ ‖poleX z.1.1 * gA z.1.1‖ * ‖poleX z.1.2 * gB z.1.2‖ * Real.exp (-2 * z.2) := by
    filter_upwards with z
    obtain ⟨⟨ξ, ξ'⟩, t⟩ := z
    simp only [Φ]
    rw [norm_mul]
    rw [show ‖poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ) * gA ξ‖ = ‖poleX ξ * gA ξ‖ * Real.exp (-t) from norm_poleX_cexp_mul gA t ξ,
        show ‖poleX ξ' * Complex.exp (-(t:ℂ) * poleX ξ') * gB ξ'‖ = ‖poleX ξ' * gB ξ'‖ * Real.exp (-t) from norm_poleX_cexp_mul gB t ξ']
    have he : Real.exp (-t) * Real.exp (-t) = Real.exp (-2 * t) := by
      rw [← Real.exp_add]; ring_nf
    rw [show ‖poleX ξ * gA ξ‖ * Real.exp (-t) * (‖poleX ξ' * gB ξ'‖ * Real.exp (-t))
        = ‖poleX ξ * gA ξ‖ * ‖poleX ξ' * gB ξ'‖ * (Real.exp (-t) * Real.exp (-t)) by ring, he]
  have hΦ : Integrable Φ ((volume.prod volume).prod (volume.restrict (Set.Ioi 0))) :=
    hPsi.mono' hmeasPhi hboundPhi
  have hL : (∫ ξ : ℝ, ∫ ξ' : ℝ,
        ((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ')) /
          (2 - 2 * Real.pi * Complex.I * (ξ + ξ')) * gA ξ * gB ξ')
      = ∫ z, Φ z ∂((volume.prod volume).prod (volume.restrict (Set.Ioi 0))) := by
    have hL1 : (∫ ξ : ℝ, ∫ ξ' : ℝ,
        ((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ')) /
          (2 - 2 * Real.pi * Complex.I * (ξ + ξ')) * gA ξ * gB ξ')
        = ∫ ξ : ℝ, ∫ ξ' : ℝ, ∫ t : ℝ in Set.Ioi 0,
            (poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ) * gA ξ) *
              (poleX ξ' * Complex.exp (-(t:ℂ) * poleX ξ') * gB ξ') := by
      apply integral_congr_ae
      filter_upwards with ξ
      apply integral_congr_ae
      filter_upwards with ξ'
      rw [hker ξ ξ']
    rw [hL1]
    rw [MeasureTheory.integral_prod Φ hΦ]
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => ∫ t : ℝ, Φ (p,t) ∂(volume.restrict (Set.Ioi 0))) hΦ.integral_prod_left]
  have hR : (∫ t : ℝ in Set.Ioi 0,
          (Complex.exp (-t) * (deriv (⇑A) t - A t)) *
            (Complex.exp (-t) * (deriv (⇑B) t - B t)))
      = ∫ z, Φ z ∂((volume.prod volume).prod (volume.restrict (Set.Ioi 0))) := by
    rw [MeasureTheory.integral_prod_symm Φ hΦ]
    show (∫ t : ℝ in Set.Ioi 0, (Complex.exp (-t) * (deriv (⇑A) t - A t)) *
            (Complex.exp (-t) * (deriv (⇑B) t - B t)))
        = ∫ t : ℝ, (∫ p : ℝ × ℝ, Φ (p,t) ∂(volume.prod volume)) ∂(volume.restrict (Set.Ioi 0))
    apply integral_congr_ae
    filter_upwards with t
    rw [show (∫ p : ℝ × ℝ, Φ (p,t) ∂(volume.prod volume))
        = ∫ p : ℝ × ℝ, (poleX p.1 * Complex.exp (-(t:ℂ) * poleX p.1) * gA p.1) *
              (poleX p.2 * Complex.exp (-(t:ℂ) * poleX p.2) * gB p.2) ∂(volume.prod volume) from rfl]
    rw [MeasureTheory.integral_prod_mul (fun ξ : ℝ => poleX ξ * Complex.exp (-(t:ℂ) * poleX ξ) * gA ξ)
        (fun ξ' : ℝ => poleX ξ' * Complex.exp (-(t:ℂ) * poleX ξ') * gB ξ')]
    rw [hgA, hgB]
    rw [keyLaplace A t, keyLaplace B t]
    have he : Complex.exp (-t) = Complex.exp (-(t:ℂ)) := by simp
    rw [he]
    ring
  rw [hL]
  exact hR.symm


end Commons.Analysis.Fourier