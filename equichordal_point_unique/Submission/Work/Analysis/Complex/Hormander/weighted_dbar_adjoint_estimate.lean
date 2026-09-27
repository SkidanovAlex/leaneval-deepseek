import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.dbarBar
import Submission.Work.Analysis.Complex.DbarCauchy.dbarBar_calculus

/-!
# The weighted Bochner--Kodaira (basic) estimate for `∂̄` on `ℂ`

This file proves `Work.Analysis.Complex.Hormander.weighted_dbar_adjoint_estimate`, the weighted
basic estimate for the Cauchy--Riemann operator (Hörmander's inequality), the analytic heart of the
weighted `L²` route to `∂̄`-solvability.

With the *unscaled* operators of `Defs.lean` (`dbar = ∂_x + i ∂_y = 2 ∂_z̄` and
`dbarBar = ∂_x - i ∂_y = 2 ∂_z`), the formal adjoint of `dbar` for the weighted measure `e^{-φ} dz`
is `u ↦ u · dbarBar φ - dbarBar u`, and the Bochner--Kodaira identity reads

  `∫ ‖dbarBar u - u · dbarBar φ‖² e^{-φ} = ∫ ‖dbar u‖² e^{-φ} + ∫ Δφ ‖u‖² e^{-φ}`.

The proof follows the second route advertised in the statement: substitute `u = y · exp (φ/2)` so
that the weight disappears, and reduce to the identity

  `∫ ‖dbarBar y - ½ y·dbarBar φ‖² = ∫ ‖dbar y + ½ y·dbar φ‖² + ∫ Δφ ‖y‖²`

for compactly supported `y`, which is proved for `C²` `y` by expanding pointwise and using the two
total divergences `0 = ∫ dbar (‖y‖² · dbarBar φ)` and (via the Wronskian identity)
`0 = ∫ ∂_y (conj y · y_x) - ∫ ∂_x (conj y · y_y)`, and then extended to `C¹` `y` by smooth
approximation with control of the first derivatives.
-/

open MeasureTheory
open scoped Topology Pointwise

noncomputable section

set_option maxHeartbeats 4000000

namespace Work.Analysis.Complex.Hormander

open Work.Analysis.Complex.DbarCauchy

/-! ## Notation: the two first partial derivatives as functions -/

/-- `∂_x f`, as a function. -/
def wda_dx (f : ℂ → ℂ) : ℂ → ℂ := fun z => (fderiv ℝ f z) 1

/-- `∂_y f`, as a function. -/
def wda_dy (f : ℂ → ℂ) : ℂ → ℂ := fun z => (fderiv ℝ f z) Complex.I

/-- `∂_x φ` for a real-valued `φ`, as a real-valued function. -/
def wda_dxr (φ : ℂ → ℝ) : ℂ → ℝ := fun z => (fderiv ℝ φ z) 1

/-- `∂_y φ` for a real-valued `φ`, as a real-valued function. -/
def wda_dyr (φ : ℂ → ℝ) : ℂ → ℝ := fun z => (fderiv ℝ φ z) Complex.I

/-- `Φ = dbar φ = φ_x + i φ_y` for a real-valued `φ`. -/
def wda_Phi (φ : ℂ → ℝ) : ℂ → ℂ := dbar (fun z => (φ z : ℂ))

/-- `Ψ = dbarBar φ = φ_x - i φ_y` for a real-valued `φ`. -/
def wda_Psi (φ : ℂ → ℝ) : ℂ → ℂ := dbarBar (fun z => (φ z : ℂ))

/-- The Laplacian `Δφ = Re (dbar (dbarBar φ))` in the workspace's normalisation. -/
def wda_lap (φ : ℂ → ℝ) : ℂ → ℝ := fun z => (dbar (wda_Psi φ) z).re

/-! ## Basic calculus facts -/

/-- The derivative of the complexification of a real-valued function. -/
theorem wda_fderiv_ofReal (φ : ℂ → ℝ) (z v : ℂ) :
    (fderiv ℝ (fun w => ((φ w : ℂ))) z) v = ((fderiv ℝ φ z) v : ℂ) := by
  by_cases h : DifferentiableAt ℝ φ z
  · have h1 : fderiv ℝ (fun w : ℂ => ((φ w : ℂ))) z
        = Complex.ofRealCLM.comp (fderiv ℝ φ z) := by
      rw [show (fun w : ℂ => ((φ w : ℂ))) = Complex.ofRealCLM ∘ φ from rfl,
        fderiv_comp z Complex.ofRealCLM.differentiableAt h, ContinuousLinearMap.fderiv]
    rw [h1]
    rfl
  · have h2 : ¬ DifferentiableAt ℝ (fun w : ℂ => ((φ w : ℂ))) z := by
      intro hd
      exact h (by
        simpa [Function.comp_def] using Complex.reCLM.differentiableAt.comp z hd)
    rw [fderiv_zero_of_not_differentiableAt h2, fderiv_zero_of_not_differentiableAt h]
    simp

@[simp] theorem wda_dx_apply (f : ℂ → ℂ) (z : ℂ) : wda_dx f z = (fderiv ℝ f z) 1 := rfl
@[simp] theorem wda_dy_apply (f : ℂ → ℂ) (z : ℂ) : wda_dy f z = (fderiv ℝ f z) Complex.I := rfl
@[simp] theorem wda_dxr_apply (φ : ℂ → ℝ) (z : ℂ) : wda_dxr φ z = (fderiv ℝ φ z) 1 := rfl
@[simp] theorem wda_dyr_apply (φ : ℂ → ℝ) (z : ℂ) : wda_dyr φ z = (fderiv ℝ φ z) Complex.I := rfl

theorem wda_dbar_apply (f : ℂ → ℂ) (z : ℂ) :
    dbar f z = wda_dx f z + Complex.I * wda_dy f z := rfl

theorem wda_dbarBar_apply (f : ℂ → ℂ) (z : ℂ) :
    dbarBar f z = wda_dx f z - Complex.I * wda_dy f z := rfl

theorem wda_Phi_apply (φ : ℂ → ℝ) (z : ℂ) :
    wda_Phi φ z = (wda_dxr φ z : ℂ) + Complex.I * (wda_dyr φ z : ℂ) := by
  rw [wda_Phi, wda_dbar_apply]
  simp only [wda_dx_apply, wda_dy_apply, wda_dxr_apply, wda_dyr_apply, wda_fderiv_ofReal]

theorem wda_Psi_apply (φ : ℂ → ℝ) (z : ℂ) :
    wda_Psi φ z = (wda_dxr φ z : ℂ) - Complex.I * (wda_dyr φ z : ℂ) := by
  rw [wda_Psi, wda_dbarBar_apply]
  simp only [wda_dx_apply, wda_dy_apply, wda_dxr_apply, wda_dyr_apply, wda_fderiv_ofReal]

@[simp] theorem wda_Phi_re (φ : ℂ → ℝ) (z : ℂ) : (wda_Phi φ z).re = wda_dxr φ z := by
  rw [wda_Phi_apply]; simp

@[simp] theorem wda_Phi_im (φ : ℂ → ℝ) (z : ℂ) : (wda_Phi φ z).im = wda_dyr φ z := by
  rw [wda_Phi_apply]; simp

@[simp] theorem wda_Psi_re (φ : ℂ → ℝ) (z : ℂ) : (wda_Psi φ z).re = wda_dxr φ z := by
  rw [wda_Psi_apply]; simp

@[simp] theorem wda_Psi_im (φ : ℂ → ℝ) (z : ℂ) : (wda_Psi φ z).im = -wda_dyr φ z := by
  rw [wda_Psi_apply]; simp

theorem wda_Psi_eq_star_Phi (φ : ℂ → ℝ) (z : ℂ) :
    wda_Psi φ z = star (wda_Phi φ z) := by
  apply Complex.ext <;> simp [wda_Phi_apply, wda_Psi_apply]

theorem wda_lap_eq (φ : ℂ → ℝ) (z : ℂ) :
    wda_lap φ z = (dbar (wda_Psi φ) z).re := rfl

/-! ## The pointwise algebraic identity -/

/-- **Pointwise Bochner--Kodaira expansion.**  For complex `A B U` and real `p q`,
`‖(A - iB) - U(p - iq)‖² - ‖(A + iB) + U(p + iq)‖² = -4 Im(A conj B) - 4 (p Re(conj A · U) + q Re(conj B · U))`. -/
theorem wda_pointwise (A B U : ℂ) (p q : ℝ) :
    ‖(A - Complex.I * B) - U * ((p : ℂ) - (q : ℂ) * Complex.I)‖ ^ 2
        - ‖(A + Complex.I * B) + U * ((p : ℂ) + (q : ℂ) * Complex.I)‖ ^ 2
      = -4 * ((A * star B).im) - 4 * (p * ((star A * U).re) + q * ((star B * U).re)) := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring


/-! ## Calculus of `Φ`, `Ψ` -/

/-- If `F` is `C²` then `z ↦ (fderiv ℝ F z) v` is `C¹`. -/
theorem wda_contDiff_fderiv_apply {F : ℂ → ℂ} (hF : ContDiff ℝ 2 F) (v : ℂ) :
    ContDiff ℝ 1 (fun z : ℂ => (fderiv ℝ F z) v) := by
  have hun : ContDiff ℝ 2 (Function.uncurry (fun (_ : ℂ) (y : ℂ) => F y)) := by
    have h : Function.uncurry (fun (_ : ℂ) (y : ℂ) => F y) = fun p : ℂ × ℂ => F p.2 := rfl
    rw [h]
    exact hF.comp contDiff_snd
  have h := ContDiff.fderiv_apply (𝕜 := ℝ) (n := 1) (m := 2)
    (f := fun (_ : ℂ) (y : ℂ) => F y) (g := fun x : ℂ => x) (k := fun _ : ℂ => v)
    hun contDiff_id contDiff_const (by norm_num)
  simpa using h

/-- `Ψ = dbarBar φ` is `C¹` when `φ` is `C²`. -/
theorem wda_contDiff_Psi (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 1 (wda_Psi φ) := by
  have hF : ContDiff ℝ 2 (fun w : ℂ => ((φ w : ℂ))) := Complex.ofRealCLM.contDiff.comp hφ
  have h1 := wda_contDiff_fderiv_apply hF (1 : ℂ)
  have h2 := wda_contDiff_fderiv_apply hF Complex.I
  have he : wda_Psi φ = fun z => (fderiv ℝ (fun w : ℂ => ((φ w : ℂ))) z) 1
      - Complex.I * (fderiv ℝ (fun w : ℂ => ((φ w : ℂ))) z) Complex.I := rfl
  rw [he]
  exact h1.sub ((contDiff_const (c := Complex.I)).mul h2)

/-- `Ψ` is differentiable when `φ` is `C²`. -/
theorem wda_differentiableAt_Psi (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (z : ℂ) :
    DifferentiableAt ℝ (wda_Psi φ) z :=
  ((wda_contDiff_Psi φ hφ).differentiable (by norm_num)).differentiableAt

/-- `z ↦ φ_x z` is continuous for `C²` `φ`. -/
theorem wda_continuous_dxr (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) : Continuous (wda_dxr φ) :=
  (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- `z ↦ φ_y z` is continuous for `C²` `φ`. -/
theorem wda_continuous_dyr (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) : Continuous (wda_dyr φ) :=
  (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- `Δφ = Re (dbar Ψ)` is continuous for `C²` `φ`. -/
theorem wda_continuous_lap (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) : Continuous (wda_lap φ) := by
  have hPsi : ContDiff ℝ 1 (wda_Psi φ) := wda_contDiff_Psi φ hφ
  have h1 : Continuous fun z => (fderiv ℝ (wda_Psi φ) z) 1 :=
    (hPsi.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h2 : Continuous fun z => (fderiv ℝ (wda_Psi φ) z) Complex.I :=
    (hPsi.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h3 : Continuous fun z =>
      (fderiv ℝ (wda_Psi φ) z) 1 + Complex.I * (fderiv ℝ (wda_Psi φ) z) Complex.I :=
    h1.add (h2.const_mul Complex.I)
  exact Complex.continuous_re.comp h3

/-- The pointwise expansion of `Re ((A + iB)(p - iq) + D·Z)` for real `A B p q D`. -/
theorem wda_re_mul_Psi (A B p q : ℝ) :
    ((((A : ℂ) + Complex.I * (B : ℂ)) * ((p : ℂ) - Complex.I * (q : ℂ))).re) = A * p + B * q := by
  simp only [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
  ring

theorem wda_dbar_re_point (A B p q : ℝ) (Z : ℂ) (D : ℝ) :
    ((((A : ℂ) + Complex.I * (B : ℂ)) * ((p : ℂ) - Complex.I * (q : ℂ)) + (D : ℂ) * Z).re)
      = A * p + B * q + D * Z.re := by
  rw [Complex.add_re, wda_re_mul_Psi, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- The derivative of the complexification of a real-valued function, at a point. -/
theorem wda_dbar_ofRealFun (F : ℂ → ℝ) (z : ℂ) :
    dbar (fun w => ((F w : ℝ) : ℂ)) z
      = (((fderiv ℝ F z) 1 : ℂ) + Complex.I * (((fderiv ℝ F z) Complex.I : ℝ) : ℂ)) := by
  rw [wda_dbar_apply]
  simp only [wda_dx_apply, wda_dy_apply, wda_fderiv_ofReal]

/-! ## The divergence identity for `‖y‖²` against `φ` -/

/-- **The divergence identity.**  For `φ` of class `C²` and `y` of class `C¹` with compact support,
`∫ (∂_x‖y‖² · φ_x + ∂_y‖y‖² · φ_y) = - ∫ Δφ · ‖y‖²`. -/
theorem wda_integral_deriv_normSq (φ : ℂ → ℝ) (y : ℂ → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hy : ContDiff ℝ 1 y) (hcs : HasCompactSupport y) :
    ∫ z, ((fderiv ℝ (fun w => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z
        + (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z) ∂volume
      = - ∫ z, wda_lap φ z * ‖y z‖ ^ 2 ∂volume := by
  set G : ℂ → ℂ := fun z => ((‖y z‖ ^ 2 : ℝ) : ℂ) * wda_Psi φ z with hGdef
  have hNsR : ContDiff ℝ 1 (fun z : ℂ => ‖y z‖ ^ 2) := ContDiff.norm_sq ℝ hy
  have hNsC : ContDiff ℝ 1 (fun z : ℂ => ((‖y z‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hNsR
  have hPsi : ContDiff ℝ 1 (wda_Psi φ) := wda_contDiff_Psi φ hφ
  have hG : ContDiff ℝ 1 G := hNsC.mul hPsi
  have hcsNs : HasCompactSupport (fun z : ℂ => ‖y z‖ ^ 2) :=
    hcs.comp_left (g := fun t : ℂ => ‖t‖ ^ 2) (by simp)
  have hcsNsC : HasCompactSupport (fun z : ℂ => ((‖y z‖ ^ 2 : ℝ) : ℂ)) :=
    hcsNs.comp_left (g := fun t : ℝ => ((t : ℂ))) (by simp)
  have hcsG : HasCompactSupport G := by
    rw [hGdef]; exact hcsNsC.mul_right (f' := wda_Psi φ)
  -- `dbar G` is continuous with compact support, hence integrable
  have hcsD : HasCompactSupport (fun z => dbar G z) := by
    have h := (hcsG.fderiv ℝ).comp_left
      (g := fun (L : ℂ →L[ℝ] ℂ) => L 1 + Complex.I * L Complex.I) (by simp)
    have h' : HasCompactSupport (fun z : ℂ =>
        (fderiv ℝ G z) 1 + Complex.I * (fderiv ℝ G z) Complex.I) := h
    have he : (fun z : ℂ => dbar G z)
        = fun z : ℂ => (fderiv ℝ G z) 1 + Complex.I * (fderiv ℝ G z) Complex.I := rfl
    rw [he]
    exact h'
  have hcontD : Continuous (fun z => dbar G z) := by
    have h1 : Continuous fun z => (fderiv ℝ G z) 1 :=
      (hG.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const : Continuous fun _ : ℂ => (1 : ℂ))
    have h2 : Continuous fun z => (fderiv ℝ G z) Complex.I :=
      (hG.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const : Continuous fun _ : ℂ => Complex.I)
    have he : (fun z => dbar G z)
        = fun z => (fderiv ℝ G z) 1 + Complex.I * (fderiv ℝ G z) Complex.I := rfl
    rw [he]
    exact h1.add (h2.const_mul Complex.I)
  have hIntD : Integrable (fun z => dbar G z) volume :=
    hcontD.integrable_of_hasCompactSupport hcsD
  have h0 : ∫ z, dbar G z ∂volume = 0 := integral_dbar_eq_zero G hG hcsG
  have hre : ∫ z, (dbar G z).re ∂volume = 0 := by
    have := Complex.reCLM.integral_comp_comm hIntD
    rw [show (∫ z, (dbar G z).re ∂volume)
        = ∫ z, Complex.reCLM (dbar G z) ∂volume from rfl, this, h0]
    simp
  -- pointwise expansion
  have hpt : ∀ z : ℂ, (dbar G z).re
      = (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z
        + (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z
        + wda_lap φ z * ‖y z‖ ^ 2 := by
    intro z
    have hd1 : DifferentiableAt ℝ (fun w : ℂ => ((‖y w‖ ^ 2 : ℝ) : ℂ)) z :=
      (hNsC.differentiable (by norm_num)).differentiableAt
    have hd2 : DifferentiableAt ℝ (wda_Psi φ) z := wda_differentiableAt_Psi φ hφ z
    have hprod : dbar (fun w : ℂ => ((‖y w‖ ^ 2 : ℝ) : ℂ) * wda_Psi φ w) z
        = dbar (fun w : ℂ => ((‖y w‖ ^ 2 : ℝ) : ℂ)) z * wda_Psi φ z
          + ((‖y z‖ ^ 2 : ℝ) : ℂ) * dbar (wda_Psi φ) z :=
      dbar_mul _ _ z hd1 hd2
    have key : (dbar G z).re
        = (dbar (fun w : ℂ => ((‖y w‖ ^ 2 : ℝ) : ℂ)) z * wda_Psi φ z).re
          + (((‖y z‖ ^ 2 : ℝ) : ℂ) * dbar (wda_Psi φ) z).re := by
      rw [show dbar G z
          = dbar (fun w : ℂ => ((‖y w‖ ^ 2 : ℝ) : ℂ) * wda_Psi φ w) z from rfl,
        hprod, Complex.add_re]
    rw [key]
    have h1 : (dbar (fun w : ℂ => ((‖y w‖ ^ 2 : ℝ) : ℂ)) z * wda_Psi φ z).re
        = (fderiv ℝ (fun w : ℂ => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z
          + (fderiv ℝ (fun w : ℂ => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z := by
      rw [wda_dbar_ofRealFun, wda_Psi_apply]
      exact wda_re_mul_Psi _ _ _ _
    have h2 : ((((‖y z‖ ^ 2 : ℝ) : ℂ) * dbar (wda_Psi φ) z).re) = wda_lap φ z * ‖y z‖ ^ 2 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      simp only [wda_lap]
      ring
    rw [h1, h2]
  have hcongr : ∫ z, (dbar G z).re ∂volume
      = ∫ z, ((fderiv ℝ (fun w => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z
        + (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z
        + wda_lap φ z * ‖y z‖ ^ 2) ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- integrability of the three pieces
  have hcontF1 : Continuous fun z : ℂ =>
      (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z :=
    ((hNsR.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      (wda_continuous_dxr φ hφ)
  have hcsF1 : HasCompactSupport fun z : ℂ =>
      (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z :=
    (hcsNs.fderiv_apply ℝ 1).mul_right (f' := wda_dxr φ)
  have hcontF2 : Continuous fun z : ℂ =>
      (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z :=
    ((hNsR.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      (wda_continuous_dyr φ hφ)
  have hcsF2 : HasCompactSupport fun z : ℂ =>
      (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z :=
    (hcsNs.fderiv_apply ℝ Complex.I).mul_right (f' := wda_dyr φ)
  have hcontF3 : Continuous fun z : ℂ => wda_lap φ z * ‖y z‖ ^ 2 :=
    (wda_continuous_lap φ hφ).mul hNsR.continuous
  have hcsF3 : HasCompactSupport fun z : ℂ => wda_lap φ z * ‖y z‖ ^ 2 :=
    hcsNs.mul_left (f := wda_lap φ)
  have hI1 : Integrable (fun z : ℂ =>
      (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z) volume :=
    hcontF1.integrable_of_hasCompactSupport hcsF1
  have hI2 : Integrable (fun z : ℂ =>
      (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z) volume :=
    hcontF2.integrable_of_hasCompactSupport hcsF2
  have hI3 : Integrable (fun z : ℂ => wda_lap φ z * ‖y z‖ ^ 2) volume :=
    hcontF3.integrable_of_hasCompactSupport hcsF3
  have hsplit : ∫ z, ((fderiv ℝ (fun w => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z
        + (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z
        + wda_lap φ z * ‖y z‖ ^ 2) ∂volume
      = (∫ z, ((fderiv ℝ (fun w => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z
        + (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z) ∂volume)
        + ∫ z, wda_lap φ z * ‖y z‖ ^ 2 ∂volume :=
    integral_add (hI1.add hI2) hI3
  rw [hcongr, hsplit] at hre
  linarith [hre]


/-! ## The chain rule for the squared norm, and the Wronskian identity -/

theorem wda_inner_eq (a b : ℂ) : inner ℝ a b = (star b * a).re := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The chain rule for `z ↦ ‖y z‖²`. -/
theorem wda_fderiv_normSq (y : ℂ → ℂ) (z v : ℂ) (hy : DifferentiableAt ℝ y z) :
    (fderiv ℝ (fun z => ‖y z‖ ^ 2) z) v = 2 * (star ((fderiv ℝ y z) v) * y z).re := by
  have hd : DifferentiableAt ℝ (fun x : ℂ => ‖x‖ ^ 2) (y z) :=
    ((contDiff_norm_sq (𝕜 := ℝ) (n := 1)).differentiable (by norm_num)).differentiableAt
  rw [show (fun z : ℂ => ‖y z‖ ^ 2) = (fun x : ℂ => ‖x‖ ^ 2) ∘ y from rfl,
    fderiv_comp z hd hy, fderiv_norm_sq]
  simp only [ContinuousLinearMap.comp_apply, Pi.smul_apply]
  rw [smul_apply, innerSL_apply_apply, wda_inner_eq]
  ring

/-- **Symmetry of the mixed partial derivatives** for a `C²` function. -/
theorem wda_mixed_partials {y : ℂ → ℂ} (hy : ContDiff ℝ 2 y) (z v w : ℂ) :
    (fderiv ℝ (fun z' => (fderiv ℝ y z') v) z) w
      = (fderiv ℝ (fun z' => (fderiv ℝ y z') w) z) v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ y) z :=
    ((hy.fderiv_right (m := 1) (n := 2) (by norm_num)).differentiable (by norm_num)).differentiableAt
  have hsym : IsSymmSndFDerivAt ℝ y z :=
    (hy.contDiffAt).isSymmSndFDerivAt (by simp [minSmoothness])
  have hc1 := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ y) (u := fun _ : ℂ => v) hd
    (differentiableAt_const v)
  have hc2 := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ y) (u := fun _ : ℂ => w) hd
    (differentiableAt_const w)
  have h1 : (fderiv ℝ (fun z' => (fderiv ℝ y z') v) z) = (fderiv ℝ (fderiv ℝ y) z).flip v := by
    rw [hc1]; simp
  have h2 : (fderiv ℝ (fun z' => (fderiv ℝ y z') w) z) = (fderiv ℝ (fderiv ℝ y) z).flip w := by
    rw [hc2]; simp
  rw [h1, h2, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact (hsym.eq v w).symm

/-- The pointwise identity `w - conj w = 2 i Im w` in the shape needed below. -/
theorem wda_point_im (A B : ℂ) :
    A * star B - B * star A = 2 * Complex.I * ((A * star B).im : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The derivative of the conjugated function: `∂_v (star ∘ y) = star (∂_v y)`. -/
theorem wda_fderiv_star (y : ℂ → ℂ) (z v : ℂ) (hy : DifferentiableAt ℝ y z) :
    (fderiv ℝ (fun z' => star (y z')) z) v = star ((fderiv ℝ y z) v) := by
  have h := hy.hasFDerivAt.star (𝕜 := ℝ)
  rw [h.fderiv]
  rfl

/-- **The Wronskian identity.**  For `y` of class `C²` with compact support,
`∫ Im (∂_x y · conj (∂_y y)) = 0`. -/
theorem wda_integral_im_deriv_mul (y : ℂ → ℂ) (hy : ContDiff ℝ 2 y)
    (hcs : HasCompactSupport y) :
    ∫ z, ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im ∂volume = 0 := by
  set F1 : ℂ → ℂ := fun z => star (y z) * (fderiv ℝ y z) 1 with hF1def
  set F2 : ℂ → ℂ := fun z => star (y z) * (fderiv ℝ y z) Complex.I with hF2def
  have hy1 : ContDiff ℝ 1 y := hy.of_le (by norm_num)
  have hstar : ContDiff ℝ 1 (fun z : ℂ => star (y z)) := by
    have hlin : ContDiff ℝ 1 (fun z : ℂ => star z) := by
      have he : (fun z : ℂ => star z) = ⇑(starL' ℝ) := by
        funext z; simp [starL']
      rw [he]
      exact (starL' ℝ).contDiff
    exact hlin.comp hy1
  have hdx : ContDiff ℝ 1 (fun z : ℂ => (fderiv ℝ y z) (1 : ℂ)) := wda_contDiff_fderiv_apply hy 1
  have hdy : ContDiff ℝ 1 (fun z : ℂ => (fderiv ℝ y z) Complex.I) :=
    wda_contDiff_fderiv_apply hy Complex.I
  have hF1 : ContDiff ℝ 1 F1 := by rw [hF1def]; exact hstar.mul hdx
  have hF2 : ContDiff ℝ 1 F2 := by rw [hF2def]; exact hstar.mul hdy
  have hcsStar : HasCompactSupport (fun z : ℂ => star (y z)) :=
    hcs.comp_left (g := fun z : ℂ => star z) (by simp)
  have hcs1 : HasCompactSupport F1 := by
    rw [hF1def]
    exact hcsStar.mul_right (f' := fun z => (fderiv ℝ y z) 1)
  have hcs2 : HasCompactSupport F2 := by
    rw [hF2def]
    exact hcsStar.mul_right (f' := fun z => (fderiv ℝ y z) Complex.I)
  have hz1 : ∫ z, (fderiv ℝ F1 z) Complex.I ∂volume = 0 :=
    integral_fderiv_eq_zero F1 hF1 hcs1 Complex.I
  have hz2 : ∫ z, (fderiv ℝ F2 z) 1 ∂volume = 0 :=
    integral_fderiv_eq_zero F2 hF2 hcs2 1
  have hcont1 : Continuous fun z => (fderiv ℝ F1 z) Complex.I :=
    (hF1.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : ℂ => Complex.I)
  have hcont2 : Continuous fun z => (fderiv ℝ F2 z) 1 :=
    (hF2.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : ℂ => (1 : ℂ))
  have hcsd1 : HasCompactSupport fun z => (fderiv ℝ F1 z) Complex.I := hcs1.fderiv_apply ℝ Complex.I
  have hcsd2 : HasCompactSupport fun z => (fderiv ℝ F2 z) 1 := hcs2.fderiv_apply ℝ 1
  have hint1 : Integrable (fun z => (fderiv ℝ F1 z) Complex.I) volume :=
    hcont1.integrable_of_hasCompactSupport hcsd1
  have hint2 : Integrable (fun z => (fderiv ℝ F2 z) 1) volume :=
    hcont2.integrable_of_hasCompactSupport hcsd2
  have hpt : ∀ z : ℂ, (fderiv ℝ F1 z) Complex.I - (fderiv ℝ F2 z) 1
      = 2 * Complex.I * (((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im : ℂ) := by
    intro z
    have hdtotal : DifferentiableAt ℝ y z := (hy.differentiable (by norm_num)).differentiableAt
    have hstarz : DifferentiableAt ℝ (fun z' : ℂ => star (y z')) z := hdtotal.star
    have hdxz : DifferentiableAt ℝ (fun z' : ℂ => (fderiv ℝ y z') (1 : ℂ)) z :=
      (hdx.differentiable one_ne_zero).differentiableAt
    have hdyz : DifferentiableAt ℝ (fun z' : ℂ => (fderiv ℝ y z') Complex.I) z :=
      (hdy.differentiable one_ne_zero).differentiableAt
    have hp1 := fderiv_fun_mul (c := fun z' : ℂ => star (y z'))
      (d := fun z' : ℂ => (fderiv ℝ y z') (1 : ℂ)) hstarz hdxz
    have hp2 := fderiv_fun_mul (c := fun z' : ℂ => star (y z'))
      (d := fun z' : ℂ => (fderiv ℝ y z') Complex.I) hstarz hdyz
    have hd1 : (fderiv ℝ F1 z) Complex.I
        = star (y z) * ((fderiv ℝ (fun z' => (fderiv ℝ y z') (1 : ℂ)) z) Complex.I)
          + ((fderiv ℝ y z) (1 : ℂ)) * ((fderiv ℝ (fun z' => star (y z')) z) Complex.I) := by
      rw [hF1def, show (fun z : ℂ => star (y z) * (fderiv ℝ y z) 1)
          = fun z => (fun z' : ℂ => star (y z')) z * (fun z' : ℂ => (fderiv ℝ y z') (1:ℂ)) z from rfl,
        hp1]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hd2 : (fderiv ℝ F2 z) 1
        = star (y z) * ((fderiv ℝ (fun z' => (fderiv ℝ y z') Complex.I) z) 1)
          + ((fderiv ℝ y z) Complex.I) * ((fderiv ℝ (fun z' => star (y z')) z) 1) := by
      rw [hF2def, show (fun z : ℂ => star (y z) * (fderiv ℝ y z) Complex.I)
          = fun z => (fun z' : ℂ => star (y z')) z * (fun z' : ℂ => (fderiv ℝ y z') Complex.I) z from rfl,
        hp2]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hsimp : (fderiv ℝ F1 z) Complex.I - (fderiv ℝ F2 z) 1
        = ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I))
          - ((fderiv ℝ y z) Complex.I * star ((fderiv ℝ y z) 1)) := by
      rw [hd1, hd2, wda_fderiv_star y z Complex.I hdtotal, wda_fderiv_star y z 1 hdtotal,
        wda_mixed_partials hy z 1 Complex.I]
      ring
    rw [hsimp]
    exact wda_point_im _ _
  have hsub : ∫ z, ((fderiv ℝ F1 z) Complex.I - (fderiv ℝ F2 z) 1) ∂volume = 0 := by
    rw [integral_sub hint1 hint2, hz1, hz2, sub_zero]
  have hcongr : ∫ z, ((fderiv ℝ F1 z) Complex.I - (fderiv ℝ F2 z) 1) ∂volume
      = ∫ z, (2 * Complex.I * (((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im : ℂ)) ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hcongr] at hsub
  rw [integral_const_mul] at hsub
  have hne : 2 * Complex.I ≠ 0 := by
    intro h
    have h2 : (2 * Complex.I).im = (2 : ℝ) := by simp
    rw [h] at h2
    simp at h2
  have hzero : ∫ z, (((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im : ℂ) ∂volume = 0 :=
    (mul_eq_zero.mp hsub).resolve_left hne
  have hcontim : Continuous fun z : ℂ =>
      (((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im : ℂ) := by
    have hc1 : Continuous fun z => (fderiv ℝ y z) 1 :=
      (hy1.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const : Continuous fun _ : ℂ => (1 : ℂ))
    have hc2 : Continuous fun z => star ((fderiv ℝ y z) Complex.I) :=
      ((hy1.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const : Continuous fun _ : ℂ => Complex.I)).star
    exact Complex.ofRealCLM.continuous.comp (Complex.continuous_im.comp (hc1.mul hc2))
  have hcsim : HasCompactSupport fun z : ℂ =>
      (((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im : ℂ) := by
    have h1 : HasCompactSupport fun z : ℂ => (fderiv ℝ y z) 1 := hcs.fderiv_apply ℝ 1
    have h2 : HasCompactSupport fun z : ℂ => star ((fderiv ℝ y z) Complex.I) :=
      (hcs.fderiv_apply ℝ Complex.I).comp_left (g := fun w : ℂ => star w) (by simp)
    exact (h1.mul_right (f' := fun z => star ((fderiv ℝ y z) Complex.I))).comp_left
      (g := fun w : ℂ => ((w.im : ℝ) : ℂ)) (by simp)
  have hintim : Integrable (fun z : ℂ =>
      (((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im : ℂ)) volume :=
    hcontim.integrable_of_hasCompactSupport hcsim
  have hre : ∫ z, ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im ∂volume = 0 := by
    have h := Complex.reCLM.integral_comp_comm hintim
    rw [show (∫ z, ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im ∂volume)
        = ∫ z, Complex.reCLM (((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im : ℂ) ∂volume
          from rfl,
      h, hzero]
    simp
  exact hre

/-! ## The Bochner--Kodaira identity for `C²` functions -/

/-- The pointwise Bochner--Kodaira expansion in the shape used below. -/
theorem wda_pointwise_y (A B U : ℂ) (p q : ℝ) :
    ‖(A - Complex.I * B) - ((1 / 2 : ℝ) : ℂ) * U * ((p : ℂ) - Complex.I * (q : ℂ))‖ ^ 2
        - ‖(A + Complex.I * B) + ((1 / 2 : ℝ) : ℂ) * U * ((p : ℂ) + Complex.I * (q : ℂ))‖ ^ 2
      = -4 * ((A * star B).im) - 2 * (p * ((star A * U).re) + q * ((star B * U).re)) := by
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- `dbar y` is compactly supported when `y` is. -/
theorem wda_hasCompactSupport_dbar {y : ℂ → ℂ} (hcs : HasCompactSupport y) :
    HasCompactSupport (fun z => dbar y z) := by
  have h := (hcs.fderiv ℝ).comp_left
    (g := fun (L : ℂ →L[ℝ] ℂ) => L 1 + Complex.I * L Complex.I) (by simp)
  have he : (fun z => dbar y z)
      = fun z => (fderiv ℝ y z) 1 + Complex.I * (fderiv ℝ y z) Complex.I := rfl
  rw [he]
  exact h

/-- `dbarBar y` is compactly supported when `y` is. -/
theorem wda_hasCompactSupport_dbarBar {y : ℂ → ℂ} (hcs : HasCompactSupport y) :
    HasCompactSupport (fun z => dbarBar y z) := by
  have h := (hcs.fderiv ℝ).comp_left
    (g := fun (L : ℂ →L[ℝ] ℂ) => L 1 - Complex.I * L Complex.I) (by simp)
  have he : (fun z => dbarBar y z)
      = fun z => (fderiv ℝ y z) 1 - Complex.I * (fderiv ℝ y z) Complex.I := rfl
  rw [he]
  exact h

/-- `Φ = dbar φ` is continuous for `C²` `φ`. -/
theorem wda_continuous_Phi (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) : Continuous (wda_Phi φ) := by
  have h1 : Continuous (wda_dxr φ) := wda_continuous_dxr φ hφ
  have h2 : Continuous (wda_dyr φ) := wda_continuous_dyr φ hφ
  have he : wda_Phi φ = fun z => (wda_dxr φ z : ℂ) + Complex.I * (wda_dyr φ z : ℂ) := by
    funext z; exact wda_Phi_apply φ z
  rw [he]
  exact (Complex.ofRealCLM.continuous.comp h1).add
    ((Complex.ofRealCLM.continuous.comp h2).const_mul Complex.I)

/-- `Ψ = dbarBar φ` is continuous for `C²` `φ`. -/
theorem wda_continuous_Psi (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) : Continuous (wda_Psi φ) :=
  (wda_contDiff_Psi φ hφ).continuous

/-- **The Bochner--Kodaira (basic) identity** for `C²` `y` with compact support:
`∫ ‖dbarBar y - ½ y·Ψ‖² = ∫ ‖dbar y + ½ y·Φ‖² + ∫ Δφ ‖y‖²`. -/
theorem wda_bochner_kodaira_c2 (φ : ℂ → ℝ) (y : ℂ → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hy : ContDiff ℝ 2 y) (hcs : HasCompactSupport y) :
    ∫ z, ‖dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z‖ ^ 2 ∂volume
      = ∫ z, ‖dbar y z + ((1 / 2 : ℝ) : ℂ) * y z * wda_Phi φ z‖ ^ 2 ∂volume
        + ∫ z, wda_lap φ z * ‖y z‖ ^ 2 ∂volume := by
  have hy1 : ContDiff ℝ 1 y := hy.of_le (by norm_num)
  have hdy : ∀ z : ℂ, DifferentiableAt ℝ y z :=
    fun z => (hy.differentiable (by norm_num)).differentiableAt
  set P : ℂ → ℝ := fun z => ‖dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z‖ ^ 2 with hP
  set Q : ℂ → ℝ := fun z => ‖dbar y z + ((1 / 2 : ℝ) : ℂ) * y z * wda_Phi φ z‖ ^ 2 with hQ
  set L : ℂ → ℝ := fun z => wda_lap φ z * ‖y z‖ ^ 2 with hL
  set AA : ℂ → ℝ := fun z => ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im with hAA
  set CC : ℂ → ℝ := fun z => wda_dxr φ z * (star ((fderiv ℝ y z) 1) * y z).re
      + wda_dyr φ z * (star ((fderiv ℝ y z) Complex.I) * y z).re with hCC
  have hΨc : Continuous (wda_Psi φ) := wda_continuous_Psi φ hφ
  have hΦc : Continuous (wda_Phi φ) := wda_continuous_Phi φ hφ
  have hdxc : Continuous fun z : ℂ => (fderiv ℝ y z) 1 :=
    (hy1.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : ℂ => (1 : ℂ))
  have hdyc : Continuous fun z : ℂ => (fderiv ℝ y z) Complex.I :=
    (hy1.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : ℂ => Complex.I)
  -- compact supports
  have hcsyΨ : HasCompactSupport fun z => ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z := by
    have h1 : HasCompactSupport fun z : ℂ => ((1 / 2 : ℝ) : ℂ) * y z :=
      hcs.mul_left (f := fun _ : ℂ => ((1 / 2 : ℝ) : ℂ))
    exact h1.mul_right (f' := wda_Psi φ)
  have hcsyΦ : HasCompactSupport fun z => ((1 / 2 : ℝ) : ℂ) * y z * wda_Phi φ z := by
    have h1 : HasCompactSupport fun z : ℂ => ((1 / 2 : ℝ) : ℂ) * y z :=
      hcs.mul_left (f := fun _ : ℂ => ((1 / 2 : ℝ) : ℂ))
    exact h1.mul_right (f' := wda_Phi φ)
  have hcsP : HasCompactSupport P := by
    rw [hP]
    exact ((wda_hasCompactSupport_dbarBar hcs).sub hcsyΨ).comp_left
      (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hcsQ : HasCompactSupport Q := by
    rw [hQ]
    exact ((wda_hasCompactSupport_dbar hcs).add hcsyΦ).comp_left
      (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hcsL : HasCompactSupport L := by
    rw [hL]
    exact (hcs.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)).mul_left (f := wda_lap φ)
  have hcsAA : HasCompactSupport AA := by
    rw [hAA]
    exact (((hcs.fderiv_apply ℝ 1).mul_right
      (f' := fun z => star ((fderiv ℝ y z) Complex.I))).comp_left
      (g := fun w : ℂ => w.im) (by simp))
  have hcsCC : HasCompactSupport CC := by
    rw [hCC]
    refine hcs.mono' ?_
    intro z hz
    refine subset_tsupport y ?_
    simp only [Function.mem_support] at hz ⊢
    intro h0
    exact hz (by simp [h0])
  -- continuity
  have hcontP : Continuous P := by
    rw [hP]
    have hdbc : Continuous fun z => dbarBar y z := by
      have he : (fun z => dbarBar y z)
          = fun z => (fderiv ℝ y z) 1 - Complex.I * (fderiv ℝ y z) Complex.I := rfl
      rw [he]; exact hdxc.sub (hdyc.const_mul Complex.I)
    exact (hdbc.sub (((continuous_const : Continuous fun _ : ℂ => ((1 / 2 : ℝ) : ℂ)).mul
      hy1.continuous).mul hΨc)).norm.pow 2
  have hcontQ : Continuous Q := by
    rw [hQ]
    have hdbc : Continuous fun z => dbar y z := by
      have he : (fun z => dbar y z)
          = fun z => (fderiv ℝ y z) 1 + Complex.I * (fderiv ℝ y z) Complex.I := rfl
      rw [he]; exact hdxc.add (hdyc.const_mul Complex.I)
    exact (hdbc.add (((continuous_const : Continuous fun _ : ℂ => ((1 / 2 : ℝ) : ℂ)).mul
      hy1.continuous).mul hΦc)).norm.pow 2
  have hcontL : Continuous L := by
    rw [hL]; exact (wda_continuous_lap φ hφ).mul (hy1.continuous.norm.pow 2)
  have hcontAA : Continuous AA := by
    rw [hAA]
    exact Complex.continuous_im.comp (hdxc.mul hdyc.star)
  have hcontCC : Continuous CC := by
    rw [hCC]
    exact (((wda_continuous_dxr φ hφ).mul
        (Complex.continuous_re.comp (hdxc.star.mul hy1.continuous))).add
      ((wda_continuous_dyr φ hφ).mul
        (Complex.continuous_re.comp (hdyc.star.mul hy1.continuous))))
  have hIP : Integrable P volume := hcontP.integrable_of_hasCompactSupport hcsP
  have hIQ : Integrable Q volume := hcontQ.integrable_of_hasCompactSupport hcsQ
  have hIL : Integrable L volume := hcontL.integrable_of_hasCompactSupport hcsL
  have hIAA : Integrable AA volume := hcontAA.integrable_of_hasCompactSupport hcsAA
  have hICC : Integrable CC volume := hcontCC.integrable_of_hasCompactSupport hcsCC
  -- the pointwise identity
  have hpt : ∀ z : ℂ, P z - Q z = -4 * AA z - 2 * CC z := by
    intro z
    revert z
    refine fun z => ?_
    rw [hP, hQ, hAA, hCC]
    dsimp only
    rw [wda_dbarBar_apply, wda_dbar_apply, wda_dx_apply, wda_dy_apply,
      wda_Psi_apply, wda_Phi_apply]
    exact wda_pointwise_y _ _ _ _ _
  -- the two integral identities
  have hW : ∫ z, AA z ∂volume = 0 := by
    rw [hAA]; exact wda_integral_im_deriv_mul y hy hcs
  have hR1 : ∫ z, (-4 * AA z) ∂volume = 0 := by
    rw [integral_const_mul, hW, mul_zero]
  have hEi := wda_integral_deriv_normSq φ y hφ hy1 hcs
  have hchain : ∫ z, ((fderiv ℝ (fun w => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z
        + (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z) ∂volume
      = 2 * ∫ z, CC z ∂volume := by
    rw [hCC, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    rw [wda_fderiv_normSq y z 1 (hdy z), wda_fderiv_normSq y z Complex.I (hdy z)]
    ring
  have hCint : ∫ z, CC z ∂volume = -(1 / 2) * ∫ z, L z ∂volume := by
    have h2 : (2 : ℝ) * (∫ z, CC z ∂volume) = -(∫ z, L z ∂volume) := by
      rw [← hL]
      rw [hchain] at hEi
      exact hEi
    calc ∫ z, CC z ∂volume = (1 / 2) * (2 * (∫ z, CC z ∂volume)) := by ring
      _ = (1 / 2) * (-(∫ z, L z ∂volume)) := by rw [h2]
      _ = -(1 / 2) * ∫ z, L z ∂volume := by ring
  -- assemble
  have hsplit1 : ∫ z, (P z - Q z) ∂volume = (∫ z, P z ∂volume) - ∫ z, Q z ∂volume :=
    integral_sub hIP hIQ
  have hsplit2 : ∫ z, (-4 * AA z - 2 * CC z) ∂volume
      = (∫ z, (-4 * AA z) ∂volume) - ∫ z, (2 * CC z) ∂volume :=
    integral_sub (hIAA.const_mul (-4)) (hICC.const_mul 2)
  have hR2 : ∫ z, (2 * CC z) ∂volume = 2 * ∫ z, CC z ∂volume := integral_const_mul 2 _
  have hcongr : ∫ z, (P z - Q z) ∂volume = ∫ z, (-4 * AA z - 2 * CC z) ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hkey : (∫ z, P z ∂volume) - (∫ z, Q z ∂volume) = ∫ z, L z ∂volume := by
    rw [← hsplit1, hcongr, hsplit2, hR1, hR2, hCint]
    ring
  simpa [add_comm] using sub_eq_iff_eq_add.mp hkey


/-! ## Smooth approximation of a compactly supported `C¹` function -/

/-- A continuous function vanishing off a closed ball is uniformly continuous, quantitatively:
there is `δ ≤ 1` so that `dist x y < δ` implies `dist (g x) (g y) < ε`. -/
theorem wda_uniform_continuous_off_ball {g : ℂ → ℂ} (hg : Continuous g) {R : ℝ}
    (hg0 : ∀ z, z ∉ Metric.closedBall (0 : ℂ) R → g z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ x y : ℂ, dist x y < δ → dist (g x) (g y) < ε := by
  have hcu : UniformContinuousOn g (Metric.closedBall (0 : ℂ) (R + 1)) :=
    (isCompact_closedBall (0 : ℂ) (R + 1)).uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.uniformContinuousOn_iff.mp hcu ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀pos one_pos, min_le_right _ _, fun x y hxy => ?_⟩
  have hx1 : dist x y < δ₀ := lt_of_lt_of_le hxy (min_le_left _ _)
  have hxy1 : dist x y < 1 := lt_of_lt_of_le hxy (min_le_right _ _)
  have hnormxy : ‖x - y‖ < 1 := by
    have h := hxy1
    rw [dist_eq_norm] at h
    exact h
  have hnormyx : ‖y - x‖ < 1 := by rw [norm_sub_rev]; exact hnormxy
  have htrix : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    have h := norm_add_le (x - y) y
    rwa [sub_add_cancel] at h
  have htriy : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    have h := norm_add_le (y - x) x
    rwa [sub_add_cancel] at h
  have key : ∀ z : ℂ, R < ‖z‖ → g z = 0 := fun z hz => hg0 z (by
    simp only [Metric.mem_closedBall, dist_zero_right]; exact not_le.mpr hz)
  by_cases hx : x ∈ Metric.closedBall (0 : ℂ) (R + 1)
  · by_cases hy : y ∈ Metric.closedBall (0 : ℂ) (R + 1)
    · exact hδ₀ x hx y hy hx1
    · have hyR : R + 1 < ‖y‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy; exact hy
      have hxR : R < ‖x‖ := by linarith
      rw [key x hxR, key y (by linarith), dist_self]; exact hε
  · have hxR : R + 1 < ‖x‖ := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx; exact hx
    have hyR : R < ‖y‖ := by linarith
    rw [key x (by linarith), key y hyR, dist_self]; exact hε


/-- **Smooth approximation of a compactly supported `C¹` function, with control of its first
partials** (obtained by convolution with a smooth bump). -/
theorem wda_contDiff_approx_of_contDiff_one {u : ℂ → ℂ} (hu : ContDiff ℝ 1 u)
    (hcs : HasCompactSupport u) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ℂ → ℂ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
      (∀ z, ‖v z - u z‖ ≤ ε) ∧
      (∀ z, ‖(fderiv ℝ v z) 1 - (fderiv ℝ u z) 1‖ ≤ ε) ∧
      (∀ z, ‖(fderiv ℝ v z) Complex.I - (fderiv ℝ u z) Complex.I‖ ≤ ε) ∧
      (∀ z, z ∈ tsupport v → ∃ w ∈ tsupport u, dist z w ≤ 1) := by
  obtain ⟨R₀, hR₀⟩ := hcs.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 with hRdef
  have hsupp : tsupport u ⊆ Metric.closedBall (0 : ℂ) R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hu0 : ∀ z, z ∉ Metric.closedBall (0 : ℂ) R → u z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hsupp h)
  have hdx : Continuous fun z : ℂ => (fderiv ℝ u z) 1 :=
    (hu.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : ℂ => (1 : ℂ))
  have hdy : Continuous fun z : ℂ => (fderiv ℝ u z) Complex.I :=
    (hu.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : ℂ => Complex.I)
  have hdx0 : ∀ z, z ∉ Metric.closedBall (0 : ℂ) R → (fderiv ℝ u z) 1 = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (f := fun x : ℂ => (fderiv ℝ u x) 1) fun h =>
      hz (hsupp (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := u) (1 : ℂ) h))
  have hdy0 : ∀ z, z ∉ Metric.closedBall (0 : ℂ) R → (fderiv ℝ u z) Complex.I = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (f := fun x : ℂ => (fderiv ℝ u x) Complex.I) fun h =>
      hz (hsupp (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := u) Complex.I h))
  obtain ⟨δ₁, hδ₁pos, hδ₁le, hδ₁⟩ := wda_uniform_continuous_off_ball hu.continuous hu0 hε
  obtain ⟨δ₂, hδ₂pos, hδ₂le, hδ₂⟩ := wda_uniform_continuous_off_ball hdx hdx0 hε
  obtain ⟨δ₃, hδ₃pos, hδ₃le, hδ₃⟩ := wda_uniform_continuous_off_ball hdy hdy0 hε
  set δ : ℝ := min δ₁ (min δ₂ δ₃) with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos (lt_min hδ₂pos hδ₃pos)
  have hδle : δ ≤ 1 := le_trans (min_le_left _ _) hδ₁le
  have hδ₂' : δ ≤ δ₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₃' : δ ≤ δ₃ := le_trans (min_le_right _ _) (min_le_right _ _)
  set ρ : ContDiffBump (0 : ℂ) := ⟨δ / 2, δ, half_pos hδpos, half_lt_self hδpos⟩ with hρdef
  have hρrOut : ρ.rOut = δ := rfl
  set v : ℂ → ℂ := convolution (ρ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume
    with hvdef
  have hv_smooth : ContDiff ℝ 2 v := by
    rw [hvdef]
    exact (ContDiffBump.hasCompactSupport_normed ρ).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (ContDiffBump.contDiff_normed (n := 2) ρ)
      hu.continuous.locallyIntegrable
  have hv_cs : HasCompactSupport v := by
    rw [hvdef]
    exact HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      (ContDiffBump.hasCompactSupport_normed ρ) hcs
  have hv_val : ∀ z, ‖v z - u z‖ ≤ ε := by
    intro z
    have h := ContDiffBump.dist_normed_convolution_le (φ := ρ) (μ := volume) (x₀ := z)
      (g := u) (ε := ε) hu.continuous.aestronglyMeasurable (fun x hx => by
        rw [Metric.mem_ball] at hx
        have hxδ : dist x z < δ := by simpa [hρrOut] using hx
        exact le_of_lt (hδ₁ x z (lt_of_lt_of_le hxδ (min_le_left _ _))))
    rw [dist_eq_norm] at h
    rw [hvdef]
    exact h
  have hderiv : ∀ z, fderiv ℝ v z = convolution (ρ.normed volume) (fderiv ℝ u)
      (ContinuousLinearMap.precompR ℂ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)) volume z := by
    intro z
    rw [hvdef]
    exact (hcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (ContDiffBump.continuous_normed ρ).locallyIntegrable hu z).fderiv
  have hcont_integrand : ∀ z : ℂ, Continuous fun t : ℂ =>
      (ContinuousLinearMap.precompR ℂ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)) (ρ.normed volume t)
        (fderiv ℝ u (z - t)) := by
    intro z
    have h1 : Continuous fun t : ℂ => (ContinuousLinearMap.precompR ℂ
        (ContinuousLinearMap.lsmul ℝ ℝ)) (ρ.normed volume t) :=
      (ContinuousLinearMap.precompR ℂ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)).continuous.comp
        (ContDiffBump.continuous_normed ρ)
    have h2 : Continuous fun t : ℂ => fderiv ℝ u (z - t) :=
      (hu.continuous_fderiv one_ne_zero).comp (by fun_prop)
    exact h1.clm_apply h2
  have hcs_integrand : ∀ z : ℂ, HasCompactSupport fun t : ℂ =>
      (ContinuousLinearMap.precompR ℂ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)) (ρ.normed volume t)
        (fderiv ℝ u (z - t)) := by
    intro z
    refine (ContDiffBump.hasCompactSupport_normed (μ := volume) ρ).mono' ?_
    intro t ht
    refine subset_tsupport (ρ.normed volume) ?_
    simp only [Function.mem_support] at ht ⊢
    intro h0
    simp only [h0, map_zero, ContinuousLinearMap.zero_apply] at ht
    exact ht rfl
  have hbridge : ∀ z : ℂ, ((convolution (ρ.normed volume) (fderiv ℝ u)
        (ContinuousLinearMap.precompR ℂ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)) volume z) (1 : ℂ))
      = convolution (ρ.normed volume) (fun z' => (fderiv ℝ u z') 1)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro z
    rw [convolution_def, convolution_def]
    rw [ContinuousLinearMap.integral_apply
      ((hcont_integrand z).integrable_of_hasCompactSupport (hcs_integrand z))]
    apply integral_congr_ae
    filter_upwards with t
    simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_one]
  have hbridgeI : ∀ z : ℂ, ((convolution (ρ.normed volume) (fderiv ℝ u)
        (ContinuousLinearMap.precompR ℂ (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)) volume z) Complex.I)
      = convolution (ρ.normed volume) (fun z' => (fderiv ℝ u z') Complex.I)
          (ContinuousLinearMap.lsmul ℝ ℝ) volume z := by
    intro z
    rw [convolution_def, convolution_def]
    rw [ContinuousLinearMap.integral_apply
      ((hcont_integrand z).integrable_of_hasCompactSupport (hcs_integrand z))]
    apply integral_congr_ae
    filter_upwards with t
    simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.lsmul_apply]
  have hv_dx : ∀ z, ‖(fderiv ℝ v z) 1 - (fderiv ℝ u z) 1‖ ≤ ε := by
    intro z
    rw [hderiv z, hbridge z]
    have h := ContDiffBump.dist_normed_convolution_le (φ := ρ) (μ := volume) (x₀ := z)
      (g := fun z' : ℂ => (fderiv ℝ u z') 1) (ε := ε) hdx.aestronglyMeasurable (fun x hx => by
        rw [Metric.mem_ball] at hx
        have hxδ : dist x z < δ := by simpa [hρrOut] using hx
        exact le_of_lt (hδ₂ x z (lt_of_lt_of_le hxδ hδ₂')))
    rw [dist_eq_norm] at h
    exact h
  have hv_dy : ∀ z, ‖(fderiv ℝ v z) Complex.I - (fderiv ℝ u z) Complex.I‖ ≤ ε := by
    intro z
    rw [hderiv z, hbridgeI z]
    have h := ContDiffBump.dist_normed_convolution_le (φ := ρ) (μ := volume) (x₀ := z)
      (g := fun z' : ℂ => (fderiv ℝ u z') Complex.I) (ε := ε) hdy.aestronglyMeasurable (fun x hx => by
        rw [Metric.mem_ball] at hx
        have hxδ : dist x z < δ := by simpa [hρrOut] using hx
        exact le_of_lt (hδ₃ x z (lt_of_lt_of_le hxδ hδ₃')))
    rw [dist_eq_norm] at h
    exact h
  have hv_supp : ∀ z, z ∈ tsupport v → ∃ w ∈ tsupport u, dist z w ≤ 1 := by
    have hsub : Function.support v ⊆ tsupport u + Metric.closedBall (0 : ℂ) ρ.rOut := by
      intro z hz
      have h1 := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
        (f := ρ.normed volume) (g := u) (by simpa [hvdef] using hz)
      obtain ⟨a, ha, b, hb, hab⟩ := h1
      refine ⟨b, subset_tsupport u hb, a, ?_, ?_⟩
      · have ha' : a ∈ Metric.ball (0 : ℂ) ρ.rOut := by
          rwa [← (ContDiffBump.support_normed_eq (μ := volume) ρ)]
        exact Metric.ball_subset_closedBall ha'
      · simpa [add_comm] using hab
    have hcomp : IsCompact (tsupport u + Metric.closedBall (0 : ℂ) ρ.rOut) :=
      hcs.isCompact.add (isCompact_closedBall (0 : ℂ) ρ.rOut)
    have hts : tsupport v ⊆ tsupport u + Metric.closedBall (0 : ℂ) ρ.rOut := by
      have hclosed : closure (tsupport u + Metric.closedBall (0 : ℂ) ρ.rOut)
          = tsupport u + Metric.closedBall (0 : ℂ) ρ.rOut := hcomp.isClosed.closure_eq
      have hcl := closure_mono hsub
      rwa [hclosed] at hcl
    intro z hz
    obtain ⟨w, hw, b, hb, hwb⟩ := hts hz
    refine ⟨w, hw, ?_⟩
    have hb' : ‖b‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hb
      exact le_trans hb hδle
    calc dist z w = dist (w + b) w := by rw [← hwb]
      _ = ‖b‖ := by rw [dist_eq_norm, add_sub_cancel_left]
      _ ≤ 1 := hb'
  exact ⟨v, hv_smooth, hv_cs, hv_val, hv_dx, hv_dy, hv_supp⟩


/-! ## The Wronskian identity for `C¹` functions, by approximation -/

/-- **The Wronskian identity for `C¹` `y` with compact support**:
`∫ Im (∂_x y · conj (∂_y y)) = 0`. -/
theorem wda_integral_im_deriv_mul_c1 (y : ℂ → ℂ) (hy : ContDiff ℝ 1 y)
    (hcs : HasCompactSupport y) :
    ∫ z, ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im ∂volume = 0 := by
  set K : Set ℂ := tsupport y + Metric.closedBall (0 : ℂ) 1 with hK
  have hKcomp : IsCompact K := hcs.isCompact.add (isCompact_closedBall (0 : ℂ) 1)
  have hKmem : ∀ z : ℂ, z ∈ tsupport y → z ∈ K := fun z hz => ⟨z, hz, 0, by simp, by simp⟩
  have hdx : Continuous fun z : ℂ => (fderiv ℝ y z) 1 :=
    (hy.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : ℂ => (1 : ℂ))
  have hdy : Continuous fun z : ℂ => (fderiv ℝ y z) Complex.I :=
    (hy.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : ℂ => Complex.I)
  have hcontF : Continuous fun z : ℂ => ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im :=
    Complex.continuous_im.comp (hdx.mul hdy.star)
  have hcsF : HasCompactSupport fun z : ℂ =>
      ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im :=
    ((hcs.fderiv_apply ℝ 1).mul_right
      (f' := fun z => star ((fderiv ℝ y z) Complex.I))).comp_left
      (g := fun w : ℂ => w.im) (by simp)
  have hFint : Integrable (fun z : ℂ =>
      ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im) volume :=
    hcontF.integrable_of_hasCompactSupport hcsF
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ,
      ‖(fderiv ℝ y z) 1‖ ≤ M ∧ ‖(fderiv ℝ y z) Complex.I‖ ≤ M := by
    obtain ⟨M₁, hM₁0, hM₁⟩ := exists_bound_of_cont_of_support (f := fun z : ℂ => (fderiv ℝ y z) 1)
      hdx (hcs.fderiv_apply ℝ 1).isCompact
      (fun z hz => image_eq_zero_of_notMem_tsupport (f := fun x : ℂ => (fderiv ℝ y x) 1) hz)
    obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound_of_cont_of_support
      (f := fun z : ℂ => (fderiv ℝ y z) Complex.I)
      hdy (hcs.fderiv_apply ℝ Complex.I).isCompact
      (fun z hz => image_eq_zero_of_notMem_tsupport (f := fun x : ℂ => (fderiv ℝ y x) Complex.I) hz)
    exact ⟨max M₁ M₂, le_max_of_le_left hM₁0, fun z =>
      ⟨le_trans (hM₁ z) (le_max_left _ _), le_trans (hM₂ z) (le_max_right _ _)⟩⟩
  have hKmeas : MeasurableSet K := hKcomp.measurableSet
  have hKind : Integrable (K.indicator (fun _ => (1 : ℝ)) : ℂ → ℝ) volume :=
    (integrable_indicator_iff hKmeas).mpr
      (integrableOn_const hKcomp.measure_lt_top.ne (by simp))
  have key : ∀ ε : ℝ, 0 < ε →
      |∫ z, ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im ∂volume|
        ≤ ((2 * M + 1) * volume.real K) * ε := by
    intro ε hε
    set ε' : ℝ := min ε 1 with hε'def
    have hε'pos : 0 < ε' := lt_min hε one_pos
    have hε'le : ε' ≤ ε := min_le_left _ _
    have hε'le1 : ε' ≤ 1 := min_le_right _ _
    obtain ⟨v, hvC2, hvcs, hv0, hv1, hv2, hvsup⟩ :=
      wda_contDiff_approx_of_contDiff_one hy hcs hε'pos
    have hvW : ∫ z, ((fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)).im ∂volume = 0 :=
      wda_integral_im_deriv_mul v hvC2 hvcs
    have hv1' : ContDiff ℝ 1 v := hvC2.of_le (by norm_num)
    have hdxv : Continuous fun z : ℂ => (fderiv ℝ v z) 1 :=
      (hv1'.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const : Continuous fun _ : ℂ => (1 : ℂ))
    have hdyv : Continuous fun z : ℂ => (fderiv ℝ v z) Complex.I :=
      (hv1'.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const : Continuous fun _ : ℂ => Complex.I)
    have hcontG : Continuous fun z : ℂ =>
        ((fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)).im :=
      Complex.continuous_im.comp (hdxv.mul hdyv.star)
    have hcsG : HasCompactSupport fun z : ℂ =>
        ((fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)).im :=
      ((hvcs.fderiv_apply ℝ 1).mul_right
        (f' := fun z => star ((fderiv ℝ v z) Complex.I))).comp_left
        (g := fun w : ℂ => w.im) (by simp)
    have hGint : Integrable (fun z : ℂ =>
        ((fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)).im) volume :=
      hcontG.integrable_of_hasCompactSupport hcsG
    have hpt : ∀ z : ℂ,
        |((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im
            - ((fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)).im|
          ≤ K.indicator (fun _ => (2 * M + 1) * ε') z := by
      intro z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz]
        have hAv : ‖(fderiv ℝ v z) 1‖ ≤ M + ε' := by
          have h1 := norm_le_norm_sub_add ((fderiv ℝ v z) 1) ((fderiv ℝ y z) 1)
          have h2 := hv1 z
          have h3 := (hM z).1
          linarith
        have hBv : ‖(fderiv ℝ v z) Complex.I‖ ≤ M + ε' := by
          have h1 := norm_le_norm_sub_add ((fderiv ℝ v z) Complex.I) ((fderiv ℝ y z) Complex.I)
          have h2 := hv2 z
          have h3 := (hM z).2
          linarith
        have hsub : star ((fderiv ℝ y z) Complex.I) - star ((fderiv ℝ v z) Complex.I)
            = star ((fderiv ℝ y z) Complex.I - (fderiv ℝ v z) Complex.I) := by simp
        have hdecomp : (fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)
              - (fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)
            = (fderiv ℝ y z) 1 * (star ((fderiv ℝ y z) Complex.I)
                - star ((fderiv ℝ v z) Complex.I))
              + ((fderiv ℝ y z) 1 - (fderiv ℝ v z) 1)
                * star ((fderiv ℝ v z) Complex.I) := by ring
        have hdiff : ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im
              - ((fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)).im
            = ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)
              - (fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)).im := by
          simp [Complex.sub_im]
        rw [hdiff]
        refine le_trans (Complex.abs_im_le_norm _) ?_
        rw [hdecomp]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, hsub]
        simp only [norm_star]
        have h1 : ‖(fderiv ℝ y z) Complex.I - (fderiv ℝ v z) Complex.I‖ ≤ ε' := by
          rw [norm_sub_rev]; exact hv2 z
        have h2 : ‖(fderiv ℝ y z) 1 - (fderiv ℝ v z) 1‖ ≤ ε' := by
          rw [norm_sub_rev]; exact hv1 z
        have hm1 := (hM z).1
        have hm2 := (hM z).2
        have hp1 := mul_le_mul hm1 h1 (norm_nonneg _) hM0
        have hp2 := mul_le_mul h2 hBv (norm_nonneg _) hε'pos.le
        nlinarith [hp1, hp2, hε'le1, hM0, hε'pos.le, mul_le_mul_of_nonneg_left hε'le1 hε'pos.le]
      · rw [Set.indicator_of_notMem hz]
        have hy0 : (fderiv ℝ y z) 1 = 0 ∧ (fderiv ℝ y z) Complex.I = 0 := by
          have hzy : z ∉ tsupport y := fun h => hz (hKmem z h)
          exact ⟨image_eq_zero_of_notMem_tsupport (f := fun x : ℂ => (fderiv ℝ y x) 1)
              (fun h => hzy (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := y) (1 : ℂ) h)),
            image_eq_zero_of_notMem_tsupport (f := fun x : ℂ => (fderiv ℝ y x) Complex.I)
              (fun h => hzy (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := y) Complex.I h))⟩
        have hv0' : (fderiv ℝ v z) 1 = 0 ∧ (fderiv ℝ v z) Complex.I = 0 := by
          have hzv : z ∉ tsupport v := fun h =>
            hz (by
              obtain ⟨w, hw, hd⟩ := hvsup z h
              refine ⟨w, hw, z - w, ?_, by simp⟩
              rw [Metric.mem_closedBall, dist_zero_right]
              rw [dist_eq_norm] at hd
              exact hd)
          exact ⟨image_eq_zero_of_notMem_tsupport (f := fun x : ℂ => (fderiv ℝ v x) 1)
              (fun h => hzv (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := v) (1 : ℂ) h)),
            image_eq_zero_of_notMem_tsupport (f := fun x : ℂ => (fderiv ℝ v x) Complex.I)
              (fun h => hzv (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := v) Complex.I h))⟩
        rw [hy0.1, hy0.2, hv0'.1, hv0'.2]
        simp
    calc |∫ z, ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im ∂volume|
        = |∫ z, (((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im
            - ((fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)).im) ∂volume| := by
          rw [integral_sub hFint hGint, hvW, sub_zero]
      _ ≤ ∫ z, |((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im
            - ((fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)).im| ∂volume := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun z : ℂ => ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im
              - ((fderiv ℝ v z) 1 * star ((fderiv ℝ v z) Complex.I)).im)
      _ ≤ ∫ z, K.indicator (fun _ => (2 * M + 1) * ε') z ∂volume :=
          integral_mono (hFint.sub hGint).abs
            ((hKind.const_mul ((2 * M + 1) * ε')).congr
              (Filter.Eventually.of_forall fun z => by
                by_cases hz : z ∈ K
                · simp [Set.indicator_of_mem hz, mul_comm]
                · simp [Set.indicator_of_notMem hz]))
            (fun z => hpt z)
      _ = (2 * M + 1) * ε' * volume.real K := by
          rw [MeasureTheory.integral_indicator_const ((2 * M + 1) * ε') hKmeas]
          simp only [smul_eq_mul]; ring
      _ ≤ ((2 * M + 1) * volume.real K) * ε := by
          have hC : 0 ≤ (2 * M + 1) * volume.real K := by
            have h1 : 0 ≤ volume.real K := by
              rw [MeasureTheory.Measure.real_def]; exact ENNReal.toReal_nonneg
            nlinarith [hM0]
          nlinarith [hε'le, hC]
  have hbound : |∫ z, ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im ∂volume| ≤ 0 := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hC : 0 ≤ (2 * M + 1) * volume.real K := by
      have h1 : 0 ≤ volume.real K := by
        rw [MeasureTheory.Measure.real_def]; exact ENNReal.toReal_nonneg
      nlinarith [hM0]
    have hδ : 0 < ε / ((2 * M + 1) * volume.real K + 1) := by positivity
    have h := key _ hδ
    have h2 : ((2 * M + 1) * volume.real K) * (ε / ((2 * M + 1) * volume.real K + 1)) ≤ ε := by
      have h3 : ((2 * M + 1) * volume.real K) / ((2 * M + 1) * volume.real K + 1) ≤ 1 := by
        rw [div_le_one (by linarith : (0 : ℝ) < (2 * M + 1) * volume.real K + 1)]
        linarith
      calc ((2 * M + 1) * volume.real K) * (ε / ((2 * M + 1) * volume.real K + 1))
          = (((2 * M + 1) * volume.real K) / ((2 * M + 1) * volume.real K + 1)) * ε := by ring
        _ ≤ 1 * ε := by nlinarith [h3, le_of_lt hε]
        _ = ε := one_mul ε
    linarith
  exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))


theorem wda_bochner_kodaira_c1 (φ : ℂ → ℝ) (y : ℂ → ℂ) (hφ : ContDiff ℝ 2 φ)
    (hy : ContDiff ℝ 1 y) (hcs : HasCompactSupport y) :
    ∫ z, ‖dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z‖ ^ 2 ∂volume
      = ∫ z, ‖dbar y z + ((1 / 2 : ℝ) : ℂ) * y z * wda_Phi φ z‖ ^ 2 ∂volume
        + ∫ z, wda_lap φ z * ‖y z‖ ^ 2 ∂volume := by
  have hy1 : ContDiff ℝ 1 y := hy
  have hdy : ∀ z : ℂ, DifferentiableAt ℝ y z :=
    fun z => (hy.differentiable (by norm_num)).differentiableAt
  set P : ℂ → ℝ := fun z => ‖dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z‖ ^ 2 with hP
  set Q : ℂ → ℝ := fun z => ‖dbar y z + ((1 / 2 : ℝ) : ℂ) * y z * wda_Phi φ z‖ ^ 2 with hQ
  set L : ℂ → ℝ := fun z => wda_lap φ z * ‖y z‖ ^ 2 with hL
  set AA : ℂ → ℝ := fun z => ((fderiv ℝ y z) 1 * star ((fderiv ℝ y z) Complex.I)).im with hAA
  set CC : ℂ → ℝ := fun z => wda_dxr φ z * (star ((fderiv ℝ y z) 1) * y z).re
      + wda_dyr φ z * (star ((fderiv ℝ y z) Complex.I) * y z).re with hCC
  have hΨc : Continuous (wda_Psi φ) := wda_continuous_Psi φ hφ
  have hΦc : Continuous (wda_Phi φ) := wda_continuous_Phi φ hφ
  have hdxc : Continuous fun z : ℂ => (fderiv ℝ y z) 1 :=
    (hy1.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : ℂ => (1 : ℂ))
  have hdyc : Continuous fun z : ℂ => (fderiv ℝ y z) Complex.I :=
    (hy1.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous fun _ : ℂ => Complex.I)
  -- compact supports
  have hcsyΨ : HasCompactSupport fun z => ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z := by
    have h1 : HasCompactSupport fun z : ℂ => ((1 / 2 : ℝ) : ℂ) * y z :=
      hcs.mul_left (f := fun _ : ℂ => ((1 / 2 : ℝ) : ℂ))
    exact h1.mul_right (f' := wda_Psi φ)
  have hcsyΦ : HasCompactSupport fun z => ((1 / 2 : ℝ) : ℂ) * y z * wda_Phi φ z := by
    have h1 : HasCompactSupport fun z : ℂ => ((1 / 2 : ℝ) : ℂ) * y z :=
      hcs.mul_left (f := fun _ : ℂ => ((1 / 2 : ℝ) : ℂ))
    exact h1.mul_right (f' := wda_Phi φ)
  have hcsP : HasCompactSupport P := by
    rw [hP]
    exact ((wda_hasCompactSupport_dbarBar hcs).sub hcsyΨ).comp_left
      (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hcsQ : HasCompactSupport Q := by
    rw [hQ]
    exact ((wda_hasCompactSupport_dbar hcs).add hcsyΦ).comp_left
      (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hcsL : HasCompactSupport L := by
    rw [hL]
    exact (hcs.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)).mul_left (f := wda_lap φ)
  have hcsAA : HasCompactSupport AA := by
    rw [hAA]
    exact (((hcs.fderiv_apply ℝ 1).mul_right
      (f' := fun z => star ((fderiv ℝ y z) Complex.I))).comp_left
      (g := fun w : ℂ => w.im) (by simp))
  have hcsCC : HasCompactSupport CC := by
    rw [hCC]
    refine hcs.mono' ?_
    intro z hz
    refine subset_tsupport y ?_
    simp only [Function.mem_support] at hz ⊢
    intro h0
    exact hz (by simp [h0])
  -- continuity
  have hcontP : Continuous P := by
    rw [hP]
    have hdbc : Continuous fun z => dbarBar y z := by
      have he : (fun z => dbarBar y z)
          = fun z => (fderiv ℝ y z) 1 - Complex.I * (fderiv ℝ y z) Complex.I := rfl
      rw [he]; exact hdxc.sub (hdyc.const_mul Complex.I)
    exact (hdbc.sub (((continuous_const : Continuous fun _ : ℂ => ((1 / 2 : ℝ) : ℂ)).mul
      hy1.continuous).mul hΨc)).norm.pow 2
  have hcontQ : Continuous Q := by
    rw [hQ]
    have hdbc : Continuous fun z => dbar y z := by
      have he : (fun z => dbar y z)
          = fun z => (fderiv ℝ y z) 1 + Complex.I * (fderiv ℝ y z) Complex.I := rfl
      rw [he]; exact hdxc.add (hdyc.const_mul Complex.I)
    exact (hdbc.add (((continuous_const : Continuous fun _ : ℂ => ((1 / 2 : ℝ) : ℂ)).mul
      hy1.continuous).mul hΦc)).norm.pow 2
  have hcontL : Continuous L := by
    rw [hL]; exact (wda_continuous_lap φ hφ).mul (hy1.continuous.norm.pow 2)
  have hcontAA : Continuous AA := by
    rw [hAA]
    exact Complex.continuous_im.comp (hdxc.mul hdyc.star)
  have hcontCC : Continuous CC := by
    rw [hCC]
    exact (((wda_continuous_dxr φ hφ).mul
        (Complex.continuous_re.comp (hdxc.star.mul hy1.continuous))).add
      ((wda_continuous_dyr φ hφ).mul
        (Complex.continuous_re.comp (hdyc.star.mul hy1.continuous))))
  have hIP : Integrable P volume := hcontP.integrable_of_hasCompactSupport hcsP
  have hIQ : Integrable Q volume := hcontQ.integrable_of_hasCompactSupport hcsQ
  have hIL : Integrable L volume := hcontL.integrable_of_hasCompactSupport hcsL
  have hIAA : Integrable AA volume := hcontAA.integrable_of_hasCompactSupport hcsAA
  have hICC : Integrable CC volume := hcontCC.integrable_of_hasCompactSupport hcsCC
  -- the pointwise identity
  have hpt : ∀ z : ℂ, P z - Q z = -4 * AA z - 2 * CC z := by
    intro z
    revert z
    refine fun z => ?_
    rw [hP, hQ, hAA, hCC]
    dsimp only
    rw [wda_dbarBar_apply, wda_dbar_apply, wda_dx_apply, wda_dy_apply,
      wda_Psi_apply, wda_Phi_apply]
    exact wda_pointwise_y _ _ _ _ _
  -- the two integral identities
  have hW : ∫ z, AA z ∂volume = 0 := by
    rw [hAA]; exact wda_integral_im_deriv_mul_c1 y hy hcs
  have hR1 : ∫ z, (-4 * AA z) ∂volume = 0 := by
    rw [integral_const_mul, hW, mul_zero]
  have hEi := wda_integral_deriv_normSq φ y hφ hy1 hcs
  have hchain : ∫ z, ((fderiv ℝ (fun w => ‖y w‖ ^ 2) z) 1 * wda_dxr φ z
        + (fderiv ℝ (fun w => ‖y w‖ ^ 2) z) Complex.I * wda_dyr φ z) ∂volume
      = 2 * ∫ z, CC z ∂volume := by
    rw [hCC, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    rw [wda_fderiv_normSq y z 1 (hdy z), wda_fderiv_normSq y z Complex.I (hdy z)]
    ring
  have hCint : ∫ z, CC z ∂volume = -(1 / 2) * ∫ z, L z ∂volume := by
    have h2 : (2 : ℝ) * (∫ z, CC z ∂volume) = -(∫ z, L z ∂volume) := by
      rw [← hL]
      rw [hchain] at hEi
      exact hEi
    calc ∫ z, CC z ∂volume = (1 / 2) * (2 * (∫ z, CC z ∂volume)) := by ring
      _ = (1 / 2) * (-(∫ z, L z ∂volume)) := by rw [h2]
      _ = -(1 / 2) * ∫ z, L z ∂volume := by ring
  -- assemble
  have hsplit1 : ∫ z, (P z - Q z) ∂volume = (∫ z, P z ∂volume) - ∫ z, Q z ∂volume :=
    integral_sub hIP hIQ
  have hsplit2 : ∫ z, (-4 * AA z - 2 * CC z) ∂volume
      = (∫ z, (-4 * AA z) ∂volume) - ∫ z, (2 * CC z) ∂volume :=
    integral_sub (hIAA.const_mul (-4)) (hICC.const_mul 2)
  have hR2 : ∫ z, (2 * CC z) ∂volume = 2 * ∫ z, CC z ∂volume := integral_const_mul 2 _
  have hcongr : ∫ z, (P z - Q z) ∂volume = ∫ z, (-4 * AA z - 2 * CC z) ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hkey : (∫ z, P z ∂volume) - (∫ z, Q z ∂volume) = ∫ z, L z ∂volume := by
    rw [← hsplit1, hcongr, hsplit2, hR1, hR2, hCint]
    ring
  simpa [add_comm] using sub_eq_iff_eq_add.mp hkey




/-! ## The substitution `u = y · exp (φ/2)` and the final estimate -/

/-- The complexification of a real-valued `C²` function. -/
theorem wda_contDiff_phiC (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (fun z : ℂ => ((φ z : ℂ))) := Complex.ofRealCLM.contDiff.comp hφ

/-- `φ/2` is `C²`. -/
theorem wda_contDiff_half (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (fun z : ℂ => ((φ z : ℂ) / 2)) := by
  have h := (wda_contDiff_phiC φ hφ).const_smul (((1 / 2 : ℝ)) : ℂ)
  convert h using 1
  ext z
  rw [smul_eq_mul]
  push_cast
  ring

/-- `-φ/2` is `C²`. -/
theorem wda_contDiff_negHalf (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (fun z : ℂ => -((φ z : ℂ) / 2)) := by
  have h := (wda_contDiff_phiC φ hφ).const_smul (((-(1 / 2) : ℝ)) : ℂ)
  convert h using 1
  ext z
  rw [smul_eq_mul]
  push_cast
  ring

/-- `exp (φ/2)` is `C²`. -/
theorem wda_contDiff_exp_half (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (fun z : ℂ => Complex.exp ((φ z : ℂ) / 2)) :=
  Complex.contDiff_exp.comp (wda_contDiff_half φ hφ)

/-- `exp (-φ/2)` is `C²`. -/
theorem wda_contDiff_exp_negHalf (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 2 (fun z : ℂ => Complex.exp (-((φ z : ℂ) / 2))) :=
  Complex.contDiff_exp.comp (wda_contDiff_negHalf φ hφ)

/-- The chain rule for `dbarBar` composed with `Complex.exp`. -/
theorem wda_dbarBar_exp (G : ℂ → ℂ) (z : ℂ) (hG : DifferentiableAt ℝ G z) :
    dbarBar (fun z => Complex.exp (G z)) z = Complex.exp (G z) * dbarBar G z := by
  have h := hG.hasFDerivAt.cexp (𝕜 := ℝ)
  rw [dbarBar, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [dbarBar]
  ring

/-- `dbarBar` is complex-homogeneous. -/
theorem wda_dbarBar_const_mul (c : ℂ) (G : ℂ → ℂ) (z : ℂ) (hG : DifferentiableAt ℝ G z) :
    dbarBar (fun z' => c * G z') z = c * dbarBar G z := by
  have h1 := dbarBar_mul (fun _ : ℂ => c) G z (differentiableAt_const c) hG
  rw [h1, dbarBar_const, zero_mul, zero_add]

/-- `dbarBar` of `φ/2` for a real-valued `C²` `φ`. -/
theorem wda_dbarBar_divTwo (φ : ℂ → ℝ) (hφ : ContDiff ℝ 2 φ) (z : ℂ) :
    dbarBar (fun z' => ((φ z' : ℂ) / 2)) z = wda_Psi φ z / 2 := by
  have hG : DifferentiableAt ℝ (fun z' : ℂ => ((φ z' : ℂ))) z :=
    Complex.ofRealCLM.differentiableAt.comp z ((hφ.differentiable (by norm_num)).differentiableAt)
  have heq : (fun z' : ℂ => ((φ z' : ℂ) / 2))
      = fun z' : ℂ => (((1 / 2 : ℝ)) : ℂ) * ((φ z' : ℂ)) := by
    funext z'; push_cast; ring
  rw [heq, wda_dbarBar_const_mul (((1 / 2 : ℝ)) : ℂ) (fun z' : ℂ => ((φ z' : ℂ))) z hG]
  rw [show dbarBar (fun z' : ℂ => ((φ z' : ℂ))) z = wda_Psi φ z from rfl]
  push_cast
  ring

theorem wda_exp_half_sq (a : ℝ) : Real.exp (a / 2) ^ 2 = Real.exp a := by
  rw [sq, ← Real.exp_add]
  ring_nf

theorem wda_exp_mul_neg (a : ℝ) : Real.exp a * Real.exp (-a) = 1 := by
  rw [← Real.exp_add]; ring_nf; exact Real.exp_zero

/-- `Real.exp a * A * Real.exp (-a) = A`. -/
theorem wda_exp_sandwich_right (a : ℝ) (A : ℝ) : Real.exp a * A * Real.exp (-a) = A := by
  rw [mul_assoc, mul_comm A (Real.exp (-a)), ← mul_assoc, wda_exp_mul_neg a, one_mul]

/-- `A * Real.exp a * Real.exp (-a) = A`. -/
theorem wda_exp_sandwich_left (a : ℝ) (A : ℝ) : A * Real.exp a * Real.exp (-a) = A := by
  rw [mul_assoc, wda_exp_mul_neg a, mul_one]


/-- **Weighted basic estimate for the Cauchy--Riemann operator** (Hörmander's inequality). -/
theorem weighted_dbar_adjoint_estimate {φ : ℂ → ℝ} {u : ℂ → ℂ} {c : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hu : ContDiff ℝ 1 u) (hucs : HasCompactSupport u)
    (hφnonneg : ∀ z, 0 ≤ φ z)
    (hc : ∀ z, c ≤ Complex.re (Work.Analysis.Complex.DbarCauchy.dbar
        (Work.Analysis.Complex.DbarCauchy.dbarBar (fun y => (φ y : ℂ))) z)) :
    c * (∫ z : ℂ, ‖u z‖ ^ 2 * Real.exp (-(φ z))) ≤
      ∫ z : ℂ, ‖Work.Analysis.Complex.DbarCauchy.dbarBar u z
          - u z * Work.Analysis.Complex.DbarCauchy.dbarBar (fun y => (φ y : ℂ)) z‖ ^ 2
        * Real.exp (-(φ z)) := by
  set h : ℂ → ℂ := fun z => Complex.exp ((φ z : ℂ) / 2) with hh
  set y : ℂ → ℂ := fun z => u z * Complex.exp (-((φ z : ℂ) / 2)) with hyy
  have hexp1 : ∀ z : ℂ, Complex.exp (-((φ z : ℂ) / 2)) * Complex.exp ((φ z : ℂ) / 2) = 1 := by
    intro z
    rw [← Complex.exp_add]
    have h0 : -((φ z : ℂ) / 2) + (φ z : ℂ) / 2 = 0 := by ring
    rw [h0, Complex.exp_zero]
  have hyu : ∀ z : ℂ, y z * h z = u z := by
    intro z
    rw [hyy, hh, mul_assoc, hexp1 z, mul_one]
  have hyC1 : ContDiff ℝ 1 y := by
    rw [hyy]
    exact hu.mul ((wda_contDiff_exp_negHalf φ hφ).of_le (by norm_num))
  have hycs : HasCompactSupport y := by
    rw [hyy]
    exact hucs.mul_right (f' := fun z => Complex.exp (-((φ z : ℂ) / 2)))
  have hhc : ContDiff ℝ 1 h := by
    rw [hh]
    exact (wda_contDiff_exp_half φ hφ).of_le (by norm_num)
  have hdy : ∀ z : ℂ, DifferentiableAt ℝ y z :=
    fun z => (hyC1.differentiable one_ne_zero).differentiableAt
  have hdh : ∀ z : ℂ, DifferentiableAt ℝ h z :=
    fun z => (hhc.differentiable one_ne_zero).differentiableAt
  have hnorm : ∀ z : ℂ, ‖h z‖ = Real.exp (φ z / 2) := by
    intro z
    rw [hh, Complex.norm_exp]
    simp
  have hdbarh : ∀ z : ℂ, dbarBar h z = h z * (wda_Psi φ z / 2) := by
    intro z
    rw [hh, wda_dbarBar_exp _ _ (((wda_contDiff_half φ hφ).differentiable
      (by norm_num)).differentiableAt)]
    rw [wda_dbarBar_divTwo φ hφ z]
  have hsub : ∀ z : ℂ, dbarBar u z - u z * wda_Psi φ z
      = h z * (dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z) := by
    intro z
    have hdu : dbarBar (fun z' => y z' * h z') z = dbarBar u z := by
      rw [show (fun z' => y z' * h z') = u from funext hyu]
    rw [← hdu, dbarBar_mul _ _ z (hdy z) (hdh z), hdbarh z, ← hyu z]
    push_cast
    ring
  have hnormu : ∀ z : ℂ, ‖dbarBar u z - u z * wda_Psi φ z‖ ^ 2 * Real.exp (-(φ z))
      = ‖dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z‖ ^ 2 := by
    intro z
    rw [hsub z, norm_mul, mul_pow, hnorm z, wda_exp_half_sq]
    exact wda_exp_sandwich_right (φ z) _
  have hnormy : ∀ z : ℂ, ‖u z‖ ^ 2 * Real.exp (-(φ z)) = ‖y z‖ ^ 2 := by
    intro z
    rw [← hyu z, norm_mul, mul_pow, hnorm z, wda_exp_half_sq]
    exact wda_exp_sandwich_left (φ z) _
  rw [show (fun z : ℂ => ‖u z‖ ^ 2 * Real.exp (-(φ z))) = fun z => ‖y z‖ ^ 2 from funext hnormy]
  rw [show (fun z : ℂ => ‖dbarBar u z - u z * dbarBar (fun y => (φ y : ℂ)) z‖ ^ 2
        * Real.exp (-(φ z)))
      = fun z => ‖dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z‖ ^ 2
      from funext hnormu]
  have hNcont : Continuous fun z : ℂ => ‖y z‖ ^ 2 := hyC1.continuous.norm.pow 2
  have hNcs : HasCompactSupport fun z : ℂ => ‖y z‖ ^ 2 :=
    hycs.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hI1 : Integrable (fun z : ℂ => wda_lap φ z * ‖y z‖ ^ 2) volume := by
    refine ((wda_continuous_lap φ hφ).mul hNcont).integrable_of_hasCompactSupport ?_
    exact hNcs.mul_left (f := wda_lap φ)
  have hI2 : Integrable (fun z : ℂ => c * ‖y z‖ ^ 2) volume := by
    refine (continuous_const.mul hNcont).integrable_of_hasCompactSupport ?_
    exact hNcs.mul_left (f := fun _ : ℂ => c)
  have hlap : c * (∫ z : ℂ, ‖y z‖ ^ 2 ∂volume) ≤ ∫ z : ℂ, wda_lap φ z * ‖y z‖ ^ 2 ∂volume := by
    rw [← integral_const_mul]
    refine integral_mono hI2 hI1 (fun z => ?_)
    exact mul_le_mul_of_nonneg_right (hc z) (by positivity)
  have hE := wda_bochner_kodaira_c1 φ y hφ hyC1 hycs
  calc c * (∫ z : ℂ, ‖y z‖ ^ 2 ∂volume) ≤ ∫ z : ℂ, wda_lap φ z * ‖y z‖ ^ 2 ∂volume := hlap
    _ ≤ ∫ z : ℂ, ‖dbarBar y z - ((1 / 2 : ℝ) : ℂ) * y z * wda_Psi φ z‖ ^ 2 ∂volume := by
        rw [hE]
        have h0 : 0 ≤ ∫ z : ℂ,
            ‖dbar y z + ((1 / 2 : ℝ) : ℂ) * y z * wda_Phi φ z‖ ^ 2 ∂volume :=
          integral_nonneg (fun z => by positivity)
        linarith

end Work.Analysis.Complex.Hormander
