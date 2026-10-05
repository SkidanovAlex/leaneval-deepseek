import Mathlib
import Submission.Work.RPV.Defs

namespace Work.RPB.B2

/-- The real part of a complex-valued path: if `U` has complex derivative `A'` at `t`
(over `ℝ`), then `s ↦ (U s).re` has derivative `A'.re`. -/
private lemma hasDerivAt_re_of_complex {U : ℝ → ℂ} {A' : ℂ} {t : ℝ}
    (hU : HasDerivAt U A' t) : HasDerivAt (fun s => (U s).re) A'.re t := by
  have h' : HasDerivAt (Complex.reCLM ∘ U)
      ((Complex.reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ A')) 1) t :=
    (Complex.reCLM.hasFDerivAt.comp t hU.hasFDerivAt).hasDerivAt
  have hder : (Complex.reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ A')) 1 = A'.re := by
    simp [ContinuousLinearMap.comp_apply, Complex.reCLM_apply]
  have hfun : (⇑Complex.reCLM ∘ U) = fun s => (U s).re := by
    funext s; simp [Function.comp, Complex.reCLM_apply]
  rw [hfun, hder] at h'
  exact h'

/-- The imaginary part of a complex-valued path: if `U` has complex derivative `A'` at `t`
(over `ℝ`), then `s ↦ (U s).im` has derivative `A'.im`. -/
private lemma hasDerivAt_im_of_complex {U : ℝ → ℂ} {A' : ℂ} {t : ℝ}
    (hU : HasDerivAt U A' t) : HasDerivAt (fun s => (U s).im) A'.im t := by
  have h' : HasDerivAt (Complex.imCLM ∘ U)
      ((Complex.imCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ A')) 1) t :=
    (Complex.imCLM.hasFDerivAt.comp t hU.hasFDerivAt).hasDerivAt
  have hder : (Complex.imCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ A')) 1 = A'.im := by
    simp [ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
  have hfun : (⇑Complex.imCLM ∘ U) = fun s => (U s).im := by
    funext s; simp [Function.comp, Complex.imCLM_apply]
  rw [hfun, hder] at h'
  exact h'

theorem hasDerivAt_chordPS_path (z w : ℝ → ℂ) (φ : ℝ → ℝ) (t : ℝ) (ζ η : ℂ) (φ' : ℝ)
    (hz : HasDerivAt z ζ t) (hw : HasDerivAt w η t) (hφ : HasDerivAt φ φ' t) :
    HasDerivAt (fun s => Work.RPV.chordPS (z s) (w s) (φ s))
      (((Complex.exp (-(φ t : ℂ) * Complex.I) *
          ((ζ + η) / (Real.sqrt 2 : ℂ) - (φ' : ℂ) * Complex.I * ((z t + w t) / (Real.sqrt 2 : ℂ)))).im, φ'),
       ((Complex.exp (-(φ t : ℂ) * Complex.I) *
          ((ζ + η) / (Real.sqrt 2 : ℂ) - (φ' : ℂ) * Complex.I * ((z t + w t) / (Real.sqrt 2 : ℂ)))).re,
        ((starRingEnd ℂ) (z t) * ζ).re + ((starRingEnd ℂ) (w t) * η).re)) t := by
  -- derivative of the complex factor `s ↦ exp(-φ(s) i) * ((z s + w s)/√2)`
  have hA : HasDerivAt
      (fun s => Complex.exp (-(φ s : ℂ) * Complex.I) * ((z s + w s) / (Real.sqrt 2 : ℂ)))
      (Complex.exp (-(φ t : ℂ) * Complex.I) *
        ((ζ + η) / (Real.sqrt 2 : ℂ) -
          (φ' : ℂ) * Complex.I * ((z t + w t) / (Real.sqrt 2 : ℂ)))) t := by
    have hinner : HasDerivAt (fun s => -(φ s : ℂ) * Complex.I) (-(φ' : ℂ) * Complex.I) t := by
      have h1 : HasDerivAt (fun s => (φ s : ℂ)) (φ' : ℂ) t := hφ.ofReal_comp
      simpa using (h1.neg).mul_const Complex.I
    have hexp : HasDerivAt (fun s => Complex.exp (-(φ s : ℂ) * Complex.I))
        (Complex.exp (-(φ t : ℂ) * Complex.I) * (-(φ' : ℂ) * Complex.I)) t := hinner.cexp
    have hzw : HasDerivAt (fun s => (z s + w s) / (Real.sqrt 2 : ℂ))
        ((ζ + η) / (Real.sqrt 2 : ℂ)) t := (hz.add hw).div_const _
    have hprod := hexp.mul hzw
    convert hprod using 1
    ring
  -- derivative of the last component `s ↦ (‖z s‖² + ‖w s‖²)/2 - 1`
  have hP2 : HasDerivAt (fun s => (‖z s‖ ^ 2 + ‖w s‖ ^ 2) / 2 - 1)
      (((starRingEnd ℂ) (z t) * ζ).re + ((starRingEnd ℂ) (w t) * η).re) t := by
    have hz2 : HasDerivAt (fun s => ‖z s‖ ^ 2) (2 * inner ℝ (z t) ζ) t := hz.norm_sq
    have hw2 : HasDerivAt (fun s => ‖w s‖ ^ 2) (2 * inner ℝ (w t) η) t := hw.norm_sq
    have hi1 : inner ℝ (z t) ζ = ((starRingEnd ℂ) (z t) * ζ).re := by
      rw [Complex.inner, mul_comm]
    have hi2 : inner ℝ (w t) η = ((starRingEnd ℂ) (w t) * η).re := by
      rw [Complex.inner, mul_comm]
    have h := ((hz2.add hw2).div_const 2).sub_const 1
    convert h using 1
    rw [hi1, hi2]; ring
  simp only [Work.RPV.chordPS]
  exact ((hasDerivAt_im_of_complex hA).prodMk hφ).prodMk
        ((hasDerivAt_re_of_complex hA).prodMk hP2)

end Work.RPB.B2
