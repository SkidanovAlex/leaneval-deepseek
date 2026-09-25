import Mathlib
import Submission.Work.Hormander.Weights.Basic

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

/-! ### Auxiliary calculus lemmas

The identity `pairing_delta` is the `(1,0)`-analogue of `pairing_dbar`: it is
obtained by computing `∂_j` of the compactly supported function
`z ↦ X z · conj(Y z) · e^{-φ z}` and using that its integral vanishes.  The
lemmas below are the same calculus statements used for `pairing_dbar`, with
`∂̄` replaced by `∂` (this changes the sign of the `φ`-term). -/

/-- `conj` of `1/2` is `1/2`. -/
private lemma conjC_half : (starRingEnd ℂ) (1/2 : ℂ) = 1/2 := by
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) from by norm_num, Complex.conj_ofReal]

/-- `star ∘ Y` is `C¹` when `Y` is. -/
private lemma contDiff_star_comp (Y : Cn n → ℂ) (hY : ContDiff ℝ 1 Y) :
    ContDiff ℝ 1 (fun z => star (Y z)) := by
  have h1 : ContDiff ℝ 1 (fun z => (Complex.conjCLE : ℂ → ℂ) (Y z)) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp hY
  simpa [Complex.conjCLE_apply, Function.comp_def] using h1

/-- `star ∘ Y` is continuous when `Y` is. -/
private lemma continuous_star_comp (Y : Cn n → ℂ) (hY : Continuous Y) :
    Continuous (fun z => star (Y z)) := by
  have := continuous_star.comp hY
  simpa [Function.comp_def] using this

/-- The complexification of the weight `e^{-φ}` is `C¹` for a `C¹` real weight. -/
private lemma contDiff_wn (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) :
    ContDiff ℝ 1 (fun z => ((wn n φ z : ℝ) : ℂ)) := by
  have h3 : ContDiff ℝ 1 (fun z : Cn n => (↑(-(φ z)) : ℂ)) :=
    (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff.comp hφ.neg
  have h2 : ContDiff ℝ 1 (fun z : Cn n => Complex.exp ((↑(-(φ z)) : ℂ))) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := (1:ℕ∞))).comp h3
  simpa [wn_apply, Complex.ofReal_exp] using h2

/-- The complexification of the weight `e^{-φ}` is continuous. -/
private lemma continuous_wn (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) :
    Continuous (fun z => ((wn n φ z : ℝ) : ℂ)) := (contDiff_wn φ hφ).continuous

/-- `∂_j X` is continuous for `C¹` functions `X`. -/
private lemma continuous_dCoord (X : Cn n → ℂ) (hX : ContDiff ℝ 1 X) (j : Fin n) :
    Continuous (fun z => dCoord n j X z) := by
  have hc : Continuous (fun z => fderiv ℝ X z) := hX.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun z => fderiv ℝ X z (evec n j)) := hc.clm_apply continuous_const
  have h2 : Continuous (fun z => fderiv ℝ X z (ivec n j)) := hc.clm_apply continuous_const
  simp only [dCoord]
  exact continuous_const.mul (h1.sub (continuous_const.mul h2))

/-- `∂̄_j X` is continuous for `C¹` functions `X`. -/
private lemma continuous_dbarCoord (X : Cn n → ℂ) (hX : ContDiff ℝ 1 X) (j : Fin n) :
    Continuous (fun z => dbarCoord n j X z) := by
  have hc : Continuous (fun z => fderiv ℝ X z) := hX.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun z => fderiv ℝ X z (evec n j)) := hc.clm_apply continuous_const
  have h2 : Continuous (fun z => fderiv ℝ X z (ivec n j)) := hc.clm_apply continuous_const
  simp only [dbarCoord]
  exact continuous_const.mul (h1.add (continuous_const.mul h2))

/-- `∂_j φ` is continuous for a `C¹` real weight. -/
private lemma continuous_dPhi (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) (j : Fin n) :
    Continuous (fun z => dPhi n j φ z) := by
  have hφc : ContDiff ℝ 1 (fun z => (φ z : ℂ)) :=
    (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contDiff.comp hφ
  have := continuous_dCoord (fun z => (φ z : ℂ)) hφc j
  simpa [dPhi] using this

/-- `∂_j X` has compact support when `X` does. -/
private lemma hasCompactSupport_dCoord (X : Cn n → ℂ) (hsX : HasCompactSupport X) (j : Fin n) :
    HasCompactSupport (fun z => dCoord n j X z) := by
  unfold dCoord
  exact (hsX.fderiv ℝ).comp_left
    (g := fun L : Cn n →L[ℝ] ℂ =>
      (1 / 2 : ℂ) * (L (evec n j) - Complex.I * L (ivec n j))) (by simp)

/-- A continuous compactly supported function times a continuous function is integrable. -/
private lemma integrable_mul_of_hasCompactSupport {f g : Cn n → ℂ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hg : Continuous g) :
    Integrable (fun z => f z * g z) :=
  (hf.mul hg).integrable_of_hasCompactSupport
    (hfs.mono (fun _ hx => Function.support_mul_subset_left f g hx))

/-- The integral of a directional derivative of a compactly supported `C¹` function vanishes. -/
private lemma integral_fderiv_eq_zero (F : Cn n → ℂ) (hF : ContDiff ℝ 1 F)
    (hs : HasCompactSupport F) (v : Cn n) : ∫ z, fderiv ℝ F z v = 0 := by
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

/-- The integral of `∂_j` of a compactly supported `C¹` function vanishes. -/
private lemma integral_dCoord_eq_zero (F : Cn n → ℂ) (hF : ContDiff ℝ 1 F)
    (hs : HasCompactSupport F) (j : Fin n) : ∫ z, dCoord n j F z = 0 := by
  have hcont : Continuous (fun z => fderiv ℝ F z) := hF.continuous_fderiv (by norm_num)
  have hI1 : Integrable (fun z => (fderiv ℝ F z) (evec n j)) :=
    (hcont.clm_apply continuous_const).integrable_of_hasCompactSupport (hs.fderiv_apply ℝ (evec n j))
  have hI2 : Integrable (fun z => (fderiv ℝ F z) (ivec n j)) :=
    (hcont.clm_apply continuous_const).integrable_of_hasCompactSupport (hs.fderiv_apply ℝ (ivec n j))
  have h1 : ∫ z, fderiv ℝ F z (evec n j) = 0 := integral_fderiv_eq_zero F hF hs (evec n j)
  have h2 : ∫ z, fderiv ℝ F z (ivec n j) = 0 := integral_fderiv_eq_zero F hF hs (ivec n j)
  have hfun : (fun z => dCoord n j F z)
      = fun z => (1/2 : ℂ) *
          ((fderiv ℝ F z) (evec n j) - Complex.I * (fderiv ℝ F z) (ivec n j)) := rfl
  rw [hfun, integral_const_mul, integral_sub hI1 (hI2.const_mul Complex.I),
      integral_const_mul, h2, h1]
  ring

/-- `∂_j` of the conjugate of a function is the conjugate of `∂̄_j`. -/
private lemma dCoord_star (Y : Cn n → ℂ) (j : Fin n) (z : Cn n) (hY : DifferentiableAt ℝ Y z) :
    dCoord n j (fun w => star (Y w)) z = star (dbarCoord n j Y z) := by
  have hfd : fderiv ℝ (fun w => star (Y w)) z
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ Y z) := by
    have h1 : (fun w => star (Y w)) = (Complex.conjCLE : ℂ → ℂ) ∘ Y := by
      funext w; rfl
    rw [h1, fderiv_comp (f := Y) z (g := (Complex.conjCLE : ℂ → ℂ))
      Complex.conjCLE.differentiableAt hY]
    rw [ContinuousLinearEquiv.fderiv]
  rw [dCoord, dbarCoord, hfd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
  rw [show (star : ℂ → ℂ) = ⇑(starRingEnd ℂ) from rfl]
  rw [map_mul, map_add, map_mul, Complex.conj_I, conjC_half]
  ring

/-- Negation rule for `∂_j`. -/
private lemma dCoord_neg (j : Fin n) (u : Cn n → ℂ) (z : Cn n) :
    dCoord n j (-u) z = -dCoord n j u z := by
  simp only [dCoord, fderiv_neg, neg_apply]
  ring

/-- Chain rule for `∂_j` and `Complex.exp ∘ ψ` (with `ψ` real valued). -/
private lemma fderiv_exp_ofReal (ψ : Cn n → ℝ) (z : Cn n) (hψ : DifferentiableAt ℝ ψ z)
    (v : Cn n) :
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

/-- Chain rule: `∂_j (exp ∘ ψ) = exp ∘ ψ · ∂_j ψ`. -/
private lemma dCoord_exp_ofReal (ψ : Cn n → ℝ) (z : Cn n) (hψ : DifferentiableAt ℝ ψ z)
    (j : Fin n) :
    dCoord n j (fun w => (Real.exp (ψ w) : ℂ)) z
      = (Real.exp (ψ z) : ℂ) * dCoord n j (fun w => (ψ w : ℂ)) z := by
  rw [dCoord, dCoord, fderiv_exp_ofReal ψ z hψ (evec n j),
    fderiv_exp_ofReal ψ z hψ (ivec n j)]
  ring

/-- `∂_j` of the complexified weight `e^{-φ}`. -/
private lemma dCoord_wn_aux (φ : Cn n → ℝ) (z : Cn n) (hφ : DifferentiableAt ℝ φ z)
    (j : Fin n) :
    dCoord n j (fun x => ((wn n φ x : ℝ) : ℂ)) z = -(((wn n φ z : ℝ) : ℂ) * dPhi n j φ z) := by
  have h := dCoord_exp_ofReal (fun x : Cn n => -(φ x)) z hφ.neg j
  have hfe : (fun x : Cn n => (((fun x : Cn n => -(φ x)) x : ℝ) : ℂ))
      = -(fun x : Cn n => (φ x : ℂ)) := by
    funext x; simp
  rw [hfe, dCoord_neg] at h
  simp only [wn_apply]
  rw [h]
  simp only [dPhi]
  ring

/-- Leibniz rule for the product `X · (conj Y · e^{-φ})` under `∂_j`. -/
private lemma dCoord_prod_star_wn (φ : Cn n → ℝ) (X Y : Cn n → ℂ) (j : Fin n) (z : Cn n)
    (hX : DifferentiableAt ℝ X z) (hY : DifferentiableAt ℝ Y z)
    (hstarY : DifferentiableAt ℝ (fun w => star (Y w)) z)
    (hw : DifferentiableAt ℝ (fun w => ((wn n φ w : ℝ) : ℂ)) z)
    (hφ : DifferentiableAt ℝ φ z) :
    dCoord n j (fun w => X w * (star (Y w) * ((wn n φ w : ℝ) : ℂ))) z
      = (dCoord n j X z - X z * dPhi n j φ z) * star (Y z) * ((wn n φ z : ℝ) : ℂ)
        + X z * star (dbarCoord n j Y z) * ((wn n φ z : ℝ) : ℂ) := by
  have h1 := dCoord_mul j X (fun w => star (Y w) * ((wn n φ w : ℝ) : ℂ)) z hX (hstarY.mul hw)
  have h2 := dCoord_mul j (fun w => star (Y w)) (fun w => ((wn n φ w : ℝ) : ℂ)) z hstarY hw
  have h3 := dCoord_star Y j z hY
  have h4 := dCoord_wn_aux φ z hφ j
  rw [h1, h2, h3, h4]
  ring

/-! ### The main identity -/

/-- **Integration by parts for `∂_j - ∂_jφ` against `∂̄_j`.**  For a real `C¹` weight `φ`
and compactly supported `C¹` functions `X`, `Y`,
`⟪(∂_j - ∂_jφ)X, Y⟫_{L²_φ} = -⟪X, ∂̄_j Y⟫_{L²_φ}`. -/
theorem pairing_delta {n : ℕ} (φ : Cn n → ℝ) (hφ : ContDiff ℝ 1 φ) (j : Fin n) (X Y : Cn n → ℂ)
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (hsX : HasCompactSupport X)
    (hsY : HasCompactSupport Y) :
    pairing0 φ (fun z => dCoord n j X z - X z * dPhi n j φ z) Y
      = -pairing0 φ X (fun z => dbarCoord n j Y z) := by
  set G : Cn n → ℂ := fun z => X z * (star (Y z) * ((wn n φ z : ℝ) : ℂ)) with hG
  have _ := hsY
  have hXz : ∀ z : Cn n, DifferentiableAt ℝ X z := fun z => (hX.differentiable_one).differentiableAt
  have hYz : ∀ z : Cn n, DifferentiableAt ℝ Y z := fun z => (hY.differentiable_one).differentiableAt
  have hsz : ∀ z : Cn n, DifferentiableAt ℝ (fun w => star (Y w)) z :=
    fun z => (contDiff_star_comp Y hY).differentiable_one.differentiableAt
  have hwz : ∀ z : Cn n, DifferentiableAt ℝ (fun w => ((wn n φ w : ℝ) : ℂ)) z :=
    fun z => (contDiff_wn φ hφ).differentiable_one.differentiableAt
  have hphiz : ∀ z : Cn n, DifferentiableAt ℝ φ z :=
    fun z => hφ.differentiable_one.differentiableAt
  have hdXcs : HasCompactSupport (fun z => dCoord n j X z) := hasCompactSupport_dCoord X hsX j
  have hGcd : ContDiff ℝ 1 G := by
    rw [hG]
    exact hX.mul ((contDiff_star_comp Y hY).mul (contDiff_wn φ hφ))
  have hGcs : HasCompactSupport G := by
    rw [hG]
    exact hsX.mono (fun x hx => Function.support_mul_subset_left X
      (fun z => star (Y z) * ((wn n φ z : ℝ) : ℂ)) hx)
  have hzero : ∫ z, dCoord n j G z = 0 := integral_dCoord_eq_zero G hGcd hGcs j
  have hpt : ∀ z, dCoord n j G z
      = (dCoord n j X z - X z * dPhi n j φ z) * star (Y z) * ((wn n φ z : ℝ) : ℂ)
        + X z * star (dbarCoord n j Y z) * ((wn n φ z : ℝ) : ℂ) := by
    intro z
    rw [hG]
    exact dCoord_prod_star_wn φ X Y j z (hXz z) (hYz z) (hsz z) (hwz z) (hphiz z)
  have hInt : ∫ z, ((dCoord n j X z - X z * dPhi n j φ z) * star (Y z)
        * ((wn n φ z : ℝ) : ℂ)
        + X z * star (dbarCoord n j Y z) * ((wn n φ z : ℝ) : ℂ)) = 0 := by
    rw [← hzero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hpt z).symm)
  have hAc : Continuous (fun z => (dCoord n j X z - X z * dPhi n j φ z) * star (Y z)) :=
    ((continuous_dCoord X hX j).sub (hX.continuous.mul (continuous_dPhi φ hφ j))).mul
      (continuous_star_comp Y hY.continuous)
  have hAcs : HasCompactSupport (fun z => (dCoord n j X z - X z * dPhi n j φ z) * star (Y z)) :=
    (hdXcs.sub (hsX.mul_right (f' := fun z => dPhi n j φ z))).mul_right
      (f' := fun z => star (Y z))
  have hIa : Integrable (fun z => (dCoord n j X z - X z * dPhi n j φ z) * star (Y z)
      * ((wn n φ z : ℝ) : ℂ)) :=
    integrable_mul_of_hasCompactSupport hAc hAcs (continuous_wn φ hφ)
  have hBcs : HasCompactSupport (fun z => X z * star (dbarCoord n j Y z)) :=
    hsX.mul_right (f' := fun z => star (dbarCoord n j Y z))
  have hIb : Integrable (fun z => X z * star (dbarCoord n j Y z) * ((wn n φ z : ℝ) : ℂ)) :=
    integrable_mul_of_hasCompactSupport
      (hX.continuous.mul (continuous_star_comp _ (continuous_dbarCoord Y hY j)))
      hBcs (continuous_wn φ hφ)
  have hsplit : ∫ z, ((dCoord n j X z - X z * dPhi n j φ z) * star (Y z)
        * ((wn n φ z : ℝ) : ℂ)
        + X z * star (dbarCoord n j Y z) * ((wn n φ z : ℝ) : ℂ))
      = (∫ z, (dCoord n j X z - X z * dPhi n j φ z) * star (Y z) * ((wn n φ z : ℝ) : ℂ))
        + (∫ z, X z * star (dbarCoord n j Y z) * ((wn n φ z : ℝ) : ℂ)) :=
    integral_add hIa hIb
  have hfin : (∫ z, (dCoord n j X z - X z * dPhi n j φ z) * star (Y z)
        * ((wn n φ z : ℝ) : ℂ))
      + (∫ z, X z * star (dbarCoord n j Y z) * ((wn n φ z : ℝ) : ℂ)) = 0 := by
    rw [← hsplit]; exact hInt
  have hA : pairing0 φ (fun z => dCoord n j X z - X z * dPhi n j φ z) Y
      = ∫ z, (dCoord n j X z - X z * dPhi n j φ z) * star (Y z) * ((wn n φ z : ℝ) : ℂ) := rfl
  have hB : pairing0 φ X (fun z => dbarCoord n j Y z)
      = ∫ z, X z * star (dbarCoord n j Y z) * ((wn n φ z : ℝ) : ℂ) := rfl
  rw [hA, hB]
  linear_combination hfin

end Work.Hormander.Weights
