import Mathlib
import Submission.Work.Hormander.Weights.Basic

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

private lemma conjC_half : (starRingEnd ℂ) (1/2 : ℂ) = 1/2 := by
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) from by norm_num, Complex.conj_ofReal]

private lemma contDiff_star_comp (Y : Cn n → ℂ) (hY : ContDiff ℝ 1 Y) :
    ContDiff ℝ 1 (fun z => star (Y z)) := by
  have h1 : ContDiff ℝ 1 (fun z => (Complex.conjCLE : ℂ → ℂ) (Y z)) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hY
  simpa [Complex.conjCLE_apply, Function.comp_def] using h1

private lemma continuous_star_comp (Y : Cn n → ℂ) (hY : Continuous Y) :
    Continuous (fun z => star (Y z)) := by
  have := continuous_star.comp hY
  simpa [Function.comp_def] using this

private lemma contDiff_wn (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) :
    ContDiff ℝ 1 (fun z => ((wn n φ z : ℝ) : ℂ)) := by
  have h3 : ContDiff ℝ 1 (fun z : Cn n => (↑(-(φ z)) : ℂ)) :=
    (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff.comp hφ.neg
  have h2 : ContDiff ℝ 1 (fun z : Cn n => Complex.exp ((↑(-(φ z)) : ℂ))) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := (1:ℕ∞))).comp h3
  simpa [wn_apply, Complex.ofReal_exp] using h2

private lemma continuous_wn (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) :
    Continuous (fun z => ((wn n φ z : ℝ) : ℂ)) := (contDiff_wn φ hφ).continuous

private lemma continuous_dbarCoord (X : Cn n → ℂ) (hX : ContDiff ℝ 1 X) (j : Fin n) :
    Continuous (fun z => dbarCoord n j X z) := by
  have hc : Continuous (fun z => fderiv ℝ X z) := hX.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun z => fderiv ℝ X z (evec n j)) := hc.clm_apply continuous_const
  have h2 : Continuous (fun z => fderiv ℝ X z (ivec n j)) := hc.clm_apply continuous_const
  simp only [dbarCoord]
  exact continuous_const.mul (h1.add (continuous_const.mul h2))

private lemma continuous_dCoord (Y : Cn n → ℂ) (hY : ContDiff ℝ 1 Y) (j : Fin n) :
    Continuous (fun z => dCoord n j Y z) := by
  have hc : Continuous (fun z => fderiv ℝ Y z) := hY.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun z => fderiv ℝ Y z (evec n j)) := hc.clm_apply continuous_const
  have h2 : Continuous (fun z => fderiv ℝ Y z (ivec n j)) := hc.clm_apply continuous_const
  simp only [dCoord]
  exact continuous_const.mul (h1.sub (continuous_const.mul h2))

private lemma continuous_dbarPhi (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) (j : Fin n) :
    Continuous (fun z => dbarPhi n j φ z) := by
  have hφc : ContDiff ℝ 1 (fun z => (φ z : ℂ)) := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff.comp hφ
  have := continuous_dbarCoord (fun z => (φ z : ℂ)) hφc j
  simpa [dbarPhi] using this

private lemma hasCompactSupport_dbarCoord (X : Cn n → ℂ) (hsX : HasCompactSupport X) (j : Fin n) :
    HasCompactSupport (fun z => dbarCoord n j X z) := by
  have h1 : HasCompactSupport (fun z => fderiv ℝ X z (evec n j)) := hsX.fderiv_apply ℝ (evec n j)
  have h2 : HasCompactSupport (fun z => fderiv ℝ X z (ivec n j)) := hsX.fderiv_apply ℝ (ivec n j)
  have h3 : HasCompactSupport (fun z => Complex.I * fderiv ℝ X z (ivec n j)) := by
    have := h2.comp_left (g := fun y : ℂ => Complex.I * y) (by simp)
    simpa [Function.comp_def] using this
  have h4 : HasCompactSupport
      (fun z => fderiv ℝ X z (evec n j) + Complex.I * fderiv ℝ X z (ivec n j)) := by
    have := h1.comp₂_left h3 (m := fun a b : ℂ => a + b) (by simp)
    simpa using this
  have h5 : HasCompactSupport
      (fun z => (1/2 : ℂ) * (fderiv ℝ X z (evec n j) + Complex.I * fderiv ℝ X z (ivec n j))) := by
    have := h4.comp_left (g := fun y : ℂ => (1/2 : ℂ) * y) (by simp)
    simpa [Function.comp_def] using this
  simpa [dbarCoord] using h5

private lemma integrable_mul_of_hasCompactSupport {f g : Cn n → ℂ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hg : Continuous g) :
    Integrable (fun z => f z * g z) :=
  (hf.mul hg).integrable_of_hasCompactSupport
    (hfs.mono (fun _ hx => Function.support_mul_subset_left f g hx))

private lemma integral_fderiv_eq_zero (F : Cn n → ℂ) (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F)
    (v : Cn n) : ∫ z, fderiv ℝ F z v = 0 := by
  have hdiff : ∀ x : Cn n, DifferentiableAt ℝ F x := fun x =>
    (hF.differentiable (by norm_num)).differentiableAt
  have hcont : Continuous (fun z => (fderiv ℝ F z) v) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsupp : HasCompactSupport (fun z => (fderiv ℝ F z) v) := hs.fderiv_apply ℝ v
  have hInt1 : Integrable (fun z => (fderiv ℝ F z) v) :=
    hcont.integrable_of_hasCompactSupport hsupp
  have hIntF : Integrable F := hF.continuous.integrable_of_hasCompactSupport hs
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Cn n => (1:ℂ)) (g := F) (v := v)
    (by simpa using (integrable_zero (Cn n) ℂ volume))
    (by simpa using hInt1)
    (by simpa using hIntF)
    (fun x _ => differentiableAt_const (c := (1:ℂ)))
    (fun x _ => hdiff x)
  simpa using h

private lemma integral_dbarCoord_eq_zero (F : Cn n → ℂ) (hF : ContDiff ℝ 1 F)
    (hs : HasCompactSupport F) (j : Fin n) : ∫ z, dbarCoord n j F z = 0 := by
  have hcont : Continuous (fun z => fderiv ℝ F z) := hF.continuous_fderiv (by norm_num)
  have hI1 : Integrable (fun z => (fderiv ℝ F z) (evec n j)) :=
    (hcont.clm_apply continuous_const).integrable_of_hasCompactSupport (hs.fderiv_apply ℝ (evec n j))
  have hI2 : Integrable (fun z => (fderiv ℝ F z) (ivec n j)) :=
    (hcont.clm_apply continuous_const).integrable_of_hasCompactSupport (hs.fderiv_apply ℝ (ivec n j))
  have h1 : ∫ z, fderiv ℝ F z (evec n j) = 0 := integral_fderiv_eq_zero F hF hs (evec n j)
  have h2 : ∫ z, fderiv ℝ F z (ivec n j) = 0 := integral_fderiv_eq_zero F hF hs (ivec n j)
  have hfun : (fun z => dbarCoord n j F z)
      = fun z => (1/2 : ℂ) * ((fderiv ℝ F z) (evec n j) + Complex.I * (fderiv ℝ F z) (ivec n j)) := rfl
  rw [hfun, integral_const_mul, integral_add hI1 (hI2.const_mul Complex.I),
      integral_const_mul, h2, h1]
  ring

private lemma dbarCoord_star (Y : Cn n → ℂ) (j : Fin n) (z : Cn n) (hY : DifferentiableAt ℝ Y z) :
    dbarCoord n j (fun w => star (Y w)) z = star (dCoord n j Y z) := by
  have hfd : fderiv ℝ (fun w => star (Y w)) z
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ Y z) := by
    have h1 : (fun w => star (Y w)) = (Complex.conjCLE : ℂ → ℂ) ∘ Y := by
      funext w; rfl
    rw [h1, fderiv_comp (f := Y) z (g := (Complex.conjCLE : ℂ → ℂ))
      Complex.conjCLE.differentiableAt hY]
    rw [ContinuousLinearEquiv.fderiv]
  rw [dbarCoord, dCoord, hfd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  rw [show (star : ℂ → ℂ) = ⇑(starRingEnd ℂ) from rfl]
  rw [map_mul, map_sub, map_mul, Complex.conj_I, conjC_half]
  ring

private lemma fderiv_exp_ofReal (ψ : Cn n → ℝ) (z : Cn n) (hψ : DifferentiableAt ℝ ψ z) (v : Cn n) :
    fderiv ℝ (fun w => (Real.exp (ψ w) : ℂ)) z v
      = (Real.exp (ψ z) : ℂ) * fderiv ℝ (fun w => (ψ w : ℂ)) z v := by
  have hΨ : HasFDerivAt (fun w : Cn n => (ψ w : ℂ))
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ ψ z)) z := by
    have h := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).hasFDerivAt.comp z hψ.hasFDerivAt
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
  have hfun : (fun w : Cn n => (Real.exp (ψ w) : ℂ)) = fun w => Complex.exp ((ψ w : ℂ)) := by
    funext w; exact Complex.ofReal_exp (ψ w)
  have hW : HasFDerivAt (fun w : Cn n => Complex.exp ((ψ w : ℂ)))
      ((Real.exp (ψ z) : ℂ) • ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ ψ z))) z := by
    have h := hΨ.cexp
    simpa [Complex.ofReal_exp] using h
  have hfderivΨ : fderiv ℝ (fun w : Cn n => (ψ w : ℂ)) z
      = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ ψ z) := hΨ.fderiv
  rw [hfun, hW.fderiv, hfderivΨ]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, Complex.ofRealCLM_apply]
  rw [Algebra.smul_def]
  simp

private lemma dbarCoord_exp_ofReal (ψ : Cn n → ℝ) (z : Cn n) (hψ : DifferentiableAt ℝ ψ z) (j : Fin n) :
    dbarCoord n j (fun w => (Real.exp (ψ w) : ℂ)) z
      = (Real.exp (ψ z) : ℂ) * dbarCoord n j (fun w => (ψ w : ℂ)) z := by
  rw [dbarCoord, dbarCoord, fderiv_exp_ofReal ψ z hψ (evec n j),
    fderiv_exp_ofReal ψ z hψ (ivec n j)]
  ring

private lemma dbarCoord_wn (φ : Cn n → ℝ) (z : Cn n) (hφ : DifferentiableAt ℝ φ z) (j : Fin n) :
    dbarCoord n j (fun x => ((wn n φ x : ℝ) : ℂ)) z
      = -(((wn n φ z : ℝ) : ℂ) * dbarPhi n j φ z) := by
  have h := dbarCoord_exp_ofReal (fun x : Cn n => -(φ x)) z hφ.neg j
  have hfe : (fun x : Cn n => (((fun x : Cn n => -(φ x)) x : ℝ) : ℂ))
      = -(fun x : Cn n => (φ x : ℂ)) := by
    funext x; simp
  rw [hfe, dbarCoord_neg] at h
  simp only [wn_apply]
  rw [h]
  simp only [dbarPhi]
  ring

private lemma dbarCoord_prod_star_wn (φ : Cn n → ℝ) (X Y : Cn n → ℂ) (j : Fin n) (z : Cn n)
    (hX : DifferentiableAt ℝ X z) (hY : DifferentiableAt ℝ Y z)
    (hstarY : DifferentiableAt ℝ (fun w => star (Y w)) z)
    (hw : DifferentiableAt ℝ (fun w => ((wn n φ w : ℝ) : ℂ)) z)
    (hφ : DifferentiableAt ℝ φ z) :
    dbarCoord n j (fun w => X w * (star (Y w) * ((wn n φ w : ℝ) : ℂ))) z
      = dbarCoord n j X z * star (Y z) * ((wn n φ z : ℝ) : ℂ)
        + X z * star (dCoord n j Y z) * ((wn n φ z : ℝ) : ℂ)
        - X z * dbarPhi n j φ z * star (Y z) * ((wn n φ z : ℝ) : ℂ) := by
  have h1 := dbarCoord_mul j X (fun w => star (Y w) * ((wn n φ w : ℝ) : ℂ)) z hX (hstarY.mul hw)
  have h2 := dbarCoord_mul j (fun w => star (Y w)) (fun w => ((wn n φ w : ℝ) : ℂ)) z hstarY hw
  have h3 := dbarCoord_star Y j z hY
  have h4 := dbarCoord_wn φ z hφ j
  rw [h1, h2, h3, h4]
  ring

private lemma integral_add_sub (A B C : Cn n → ℂ) (hA : Integrable A) (hB : Integrable B)
    (hC : Integrable C) :
    ∫ z, (A z + B z - C z) = (∫ z, A z) + (∫ z, B z) - (∫ z, C z) := by
  rw [integral_sub (f := fun z => A z + B z) (g := C) (hA.add hB) hC,
      integral_add (f := A) (g := B) hA hB]

theorem pairing_dbar {n : ℕ} (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) (j : Fin n) (X Y : Cn n → ℂ)
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (hsX : HasCompactSupport X)
    (hsY : HasCompactSupport Y) :
    pairing0 φ (fun z => dbarCoord n j X z) Y
      = -pairing0 φ X (fun z => dCoord n j Y z)
        + pairing0 φ (fun z => X z * dbarPhi n j φ z) Y := by
  set G : Cn n → ℂ := fun z => X z * (star (Y z) * ((wn n φ z : ℝ) : ℂ)) with hG
  have _ := hsY
  have hXz : ∀ z : Cn n, DifferentiableAt ℝ X z := fun z => (hX.differentiable_one).differentiableAt
  have hYz : ∀ z : Cn n, DifferentiableAt ℝ Y z := fun z => (hY.differentiable_one).differentiableAt
  have hsz : ∀ z : Cn n, DifferentiableAt ℝ (fun w => star (Y w)) z :=
    fun z => (contDiff_star_comp Y hY).differentiable_one.differentiableAt
  have hwz : ∀ z : Cn n, DifferentiableAt ℝ (fun w => ((wn n φ w : ℝ) : ℂ)) z :=
    fun z => (contDiff_wn φ hφ).differentiable_one.differentiableAt
  have hphiz : ∀ z : Cn n, DifferentiableAt ℝ φ z := fun z => hφ.differentiable_one.differentiableAt
  have hdXcs : HasCompactSupport (fun z => dbarCoord n j X z) := hasCompactSupport_dbarCoord X hsX j
  have hGcd : ContDiff ℝ 1 G := by
    rw [hG]
    exact hX.mul ((contDiff_star_comp Y hY).mul (contDiff_wn φ hφ))
  have hGcs : HasCompactSupport G := by
    rw [hG]
    exact hsX.mono (fun x hx => Function.support_mul_subset_left X
      (fun z => star (Y z) * ((wn n φ z : ℝ) : ℂ)) hx)
  have hzero : ∫ z, dbarCoord n j G z = 0 := integral_dbarCoord_eq_zero G hGcd hGcs j
  have hpt : ∀ z, dbarCoord n j G z
      = dbarCoord n j X z * star (Y z) * ((wn n φ z : ℝ) : ℂ)
        + X z * star (dCoord n j Y z) * ((wn n φ z : ℝ) : ℂ)
        - X z * dbarPhi n j φ z * star (Y z) * ((wn n φ z : ℝ) : ℂ) := by
    intro z
    rw [hG]
    exact dbarCoord_prod_star_wn φ X Y j z (hXz z) (hYz z) (hsz z) (hwz z) (hphiz z)
  have hInt : ∫ z, (dbarCoord n j X z * star (Y z) * ((wn n φ z : ℝ) : ℂ)
        + X z * star (dCoord n j Y z) * ((wn n φ z : ℝ) : ℂ)
        - X z * dbarPhi n j φ z * star (Y z) * ((wn n φ z : ℝ) : ℂ)) = 0 := by
    rw [← hzero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hpt z).symm)
  have hAc : Continuous (fun z => dbarCoord n j X z * star (Y z)) :=
    (continuous_dbarCoord X hX j).mul (continuous_star_comp Y hY.continuous)
  have hAcs : HasCompactSupport (fun z => dbarCoord n j X z * star (Y z)) :=
    hdXcs.mono (fun x hx => Function.support_mul_subset_left
      (fun z => dbarCoord n j X z) (fun z => star (Y z)) hx)
  have hIa : Integrable (fun z => dbarCoord n j X z * star (Y z) * ((wn n φ z : ℝ) : ℂ)) :=
    integrable_mul_of_hasCompactSupport hAc hAcs (continuous_wn φ hφ)
  have hBcs : HasCompactSupport (fun z => X z * star (dCoord n j Y z)) :=
    hsX.mono (fun x hx => Function.support_mul_subset_left X (fun z => star (dCoord n j Y z)) hx)
  have hIb : Integrable (fun z => X z * star (dCoord n j Y z) * ((wn n φ z : ℝ) : ℂ)) :=
    integrable_mul_of_hasCompactSupport (hX.continuous.mul
      (continuous_star_comp _ (continuous_dCoord Y hY j))) hBcs (continuous_wn φ hφ)
  have hCcs : HasCompactSupport (fun z => X z * dbarPhi n j φ z * star (Y z)) :=
    hsX.mono (fun x hx => Function.support_mul_subset_left X (fun z => dbarPhi n j φ z)
      (Function.support_mul_subset_left (fun z => X z * dbarPhi n j φ z)
        (fun z => star (Y z)) hx))
  have hIc : Integrable (fun z => X z * dbarPhi n j φ z * star (Y z) * ((wn n φ z : ℝ) : ℂ)) :=
    integrable_mul_of_hasCompactSupport
      ((hX.continuous.mul (continuous_dbarPhi φ hφ j)).mul (continuous_star_comp Y hY.continuous))
      hCcs (continuous_wn φ hφ)
  have hsplit : ∫ z, (dbarCoord n j X z * star (Y z) * ((wn n φ z : ℝ) : ℂ)
        + X z * star (dCoord n j Y z) * ((wn n φ z : ℝ) : ℂ)
        - X z * dbarPhi n j φ z * star (Y z) * ((wn n φ z : ℝ) : ℂ))
      = (∫ z, dbarCoord n j X z * star (Y z) * ((wn n φ z : ℝ) : ℂ))
        + (∫ z, X z * star (dCoord n j Y z) * ((wn n φ z : ℝ) : ℂ))
        - (∫ z, X z * dbarPhi n j φ z * star (Y z) * ((wn n φ z : ℝ) : ℂ)) :=
    integral_add_sub _ _ _ hIa hIb hIc
  have hfin : (∫ z, dbarCoord n j X z * star (Y z) * ((wn n φ z : ℝ) : ℂ))
      + (∫ z, X z * star (dCoord n j Y z) * ((wn n φ z : ℝ) : ℂ))
      - (∫ z, X z * dbarPhi n j φ z * star (Y z) * ((wn n φ z : ℝ) : ℂ)) = 0 := by
    rw [← hsplit]; exact hInt
  have hA : pairing0 φ (fun z => dbarCoord n j X z) Y
      = ∫ z, dbarCoord n j X z * star (Y z) * ((wn n φ z : ℝ) : ℂ) := rfl
  have hB : pairing0 φ X (fun z => dCoord n j Y z)
      = ∫ z, X z * star (dCoord n j Y z) * ((wn n φ z : ℝ) : ℂ) := rfl
  have hC : pairing0 φ (fun z => X z * dbarPhi n j φ z) Y
      = ∫ z, X z * dbarPhi n j φ z * star (Y z) * ((wn n φ z : ℝ) : ℂ) := rfl
  rw [hA, hB, hC]
  linear_combination hfin

end Work.Hormander.Weights

