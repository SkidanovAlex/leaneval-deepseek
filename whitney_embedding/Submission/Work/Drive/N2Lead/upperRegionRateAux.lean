import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2Lead.modelArc_im_strictMonoOn
import Submission.Work.Drive.N2Lead.modelArc_cross_about_one
import Submission.Work.Drive.N2Lead.mobiusGeomDefs

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

noncomputable section

/-! ## Pure calculus helpers for the model map `saddlePhi` -/

/-- The derivative of `ζ ↦ η + ζ.re` is `Complex.reCLM`. -/
lemma fderiv_add_re (η : ℝ) (ζ : ℂ) :
    fderiv ℝ (fun z : ℂ => η + z.re) ζ = Complex.reCLM := by
  rw [fderiv_const_add (𝕜 := ℝ) (E := ℂ) (F := ℝ) (f := fun z : ℂ => z.re) (x := ζ) η]
  exact ContinuousLinearMap.fderiv Complex.reCLM

/-- The derivative of `ζ ↦ saddleM δ ζ.im` is `(deriv (saddleM δ) ζ.im) • imCLM`. -/
lemma fderiv_saddleM_im (δ : ℝ) (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ) (ζ : ℂ) :
    fderiv ℝ (fun z : ℂ => saddleM δ z.im) ζ = (deriv (saddleM δ) ζ.im) • Complex.imCLM := by
  have hd : DifferentiableAt ℝ (saddleM δ) ζ.im :=
    ((contDiff_saddleM hδ h2).differentiable (by simp)).differentiableAt
  have hdc : DifferentiableAt ℝ (Complex.imCLM : ℂ → ℝ) ζ := Complex.imCLM.differentiableAt
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := ζ) (f := (Complex.imCLM : ℂ → ℝ)) (g := (saddleM δ))
    hd hdc
  rw [show (fun z : ℂ => saddleM δ z.im) = (saddleM δ) ∘ (Complex.imCLM : ℂ → ℝ) from rfl,
    hcomp, ContinuousLinearMap.fderiv (x := ζ)]
  ext h
  rw [ContinuousLinearMap.comp_apply, smul_apply, Complex.imCLM_apply,
    fderiv_eq_smul_deriv, smul_eq_mul, smul_eq_mul]
  ring

/-- The derivative of the model map `saddlePhi η δ`, in coordinates. -/
lemma fderiv_saddlePhi_apply {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ) (ζ h : ℂ) :
    fderiv ℝ (saddlePhi η δ) ζ h
      = h - ((saddleM δ ζ.im * h.re + (η + ζ.re) * (deriv (saddleM δ) ζ.im * h.im) : ℝ) : ℂ) := by
  have hMd : DifferentiableAt ℝ (saddleM δ) ζ.im :=
    ((contDiff_saddleM hδ h2).differentiable (by simp)).differentiableAt
  have hdc : DifferentiableAt ℝ (Complex.imCLM : ℂ → ℝ) ζ := Complex.imCLM.differentiableAt
  have hud : DifferentiableAt ℝ (fun z : ℂ => saddleM δ z.im) ζ := hMd.comp ζ hdc
  have hvd : DifferentiableAt ℝ (fun z : ℂ => η + z.re) ζ :=
    (differentiableAt_const η).add Complex.reCLM.differentiableAt
  have hwd : DifferentiableAt ℝ (fun z : ℂ => saddleM δ z.im * (η + z.re)) ζ := hud.mul hvd
  have hw : fderiv ℝ (fun z : ℂ => saddleM δ z.im * (η + z.re)) ζ h
      = saddleM δ ζ.im * h.re + (η + ζ.re) * (deriv (saddleM δ) ζ.im * h.im) := by
    rw [show (fun z : ℂ => saddleM δ z.im * (η + z.re))
        = (fun z : ℂ => saddleM δ z.im) * (fun z : ℂ => η + z.re) from rfl,
      fderiv_mul hud hvd, fderiv_saddleM_im δ hδ h2 ζ, fderiv_add_re η ζ]
    simp only [add_apply, smul_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  have huc : DifferentiableAt ℝ (fun z : ℂ => ((saddleM δ z.im * (η + z.re) : ℝ) : ℂ)) ζ :=
    Complex.ofRealCLM.differentiableAt.comp ζ hwd
  have hu : fderiv ℝ (fun z : ℂ => ((saddleM δ z.im * (η + z.re) : ℝ) : ℂ)) ζ h
      = ((saddleM δ ζ.im * h.re + (η + ζ.re) * (deriv (saddleM δ) ζ.im * h.im) : ℝ) : ℂ) := by
    rw [show (fun z : ℂ => ((saddleM δ z.im * (η + z.re) : ℝ) : ℂ))
        = (⇑Complex.ofRealCLM) ∘ (fun z : ℂ => saddleM δ z.im * (η + z.re)) from rfl,
      fderiv_comp (𝕜 := ℝ) ζ (g := ⇑Complex.ofRealCLM)
        (f := fun z : ℂ => saddleM δ z.im * (η + z.re)) Complex.ofRealCLM.differentiableAt hwd,
      ContinuousLinearMap.fderiv (f := Complex.ofRealCLM) (x := saddleM δ ζ.im * (η + ζ.re)),
      ContinuousLinearMap.comp_apply, hw, Complex.ofRealCLM_apply]
  have hfun : (saddlePhi η δ) = id - fun z : ℂ => ((saddleM δ z.im * (η + z.re) : ℝ) : ℂ) := by
    funext z
    rw [Pi.sub_apply, id]
    exact saddlePhi_eq_sub η δ z
  rw [hfun, fderiv_sub (differentiableAt_id (x := ζ)) huc, fderiv_id]
  simp only [sub_apply, ContinuousLinearMap.id_apply, hu]

/-- The derivative of `saddlePhi η δ` in a purely imaginary direction, in terms of the model
arc coordinate. -/
lemma fderiv_saddlePhi_mul_I {η δ s : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ) (ζ : ℂ) :
    fderiv ℝ (saddlePhi η δ) ζ ((s : ℂ) * Complex.I)
      = s • (((deriv (modelSigma η δ ζ.re) ζ.im : ℝ) : ℂ) + Complex.I) := by
  rw [fderiv_saddlePhi_apply hδ h2 ζ ((s : ℂ) * Complex.I)]
  have hre : (((s : ℂ) * Complex.I).re) = 0 := by simp
  have him : (((s : ℂ) * Complex.I).im) = s := by simp
  rw [hre, him, deriv_modelSigma' hδ h2 ζ.im, Complex.real_smul]
  push_cast
  ring

end

/-- The derivative of `ζ ↦ lam * (ζ²).re`, evaluated in coordinates. -/
lemma fderiv_smul_sq_re_apply (lam : ℝ) (z w : ℂ) :
    (fderiv ℝ (fun ζ : ℂ => lam * (ζ ^ 2).re) z) w = lam * ((2 * z * w).re) := by
  have hdiff : DifferentiableAt ℝ (fun ζ : ℂ => (ζ ^ 2).re) z := by fun_prop
  have hfs : fderiv ℝ (fun ζ : ℂ => lam * (ζ ^ 2).re) z
      = lam • fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) z := by
    rw [show (fun ζ : ℂ => lam * (ζ ^ 2).re) = lam • (fun ζ : ℂ => (ζ ^ 2).re) from rfl,
      fderiv_const_smul hdiff]
  rw [hfs, smul_apply, smul_eq_mul, fderiv_sq_re_apply]

/-- The real part of the derivative of `ζ ↦ ζ²` is the derivative of `ζ ↦ (ζ²).re`. -/
lemma re_fderiv_sq (z w : ℂ) :
    ((fderiv ℝ (fun ζ : ℂ => ζ ^ 2) z) w).re = (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) z) w := by
  rw [fderiv_sq_apply, fderiv_sq_re_apply]

/-- Scalar multiplication of a continuous linear form, evaluated. -/
lemma smul_apply_real (c : ℝ) (L : ℂ →L[ℝ] ℝ) (x : ℂ) : (c • L) x = c * L x := by
  rw [smul_apply, smul_eq_mul]

end Work.Drive.N2Lead
