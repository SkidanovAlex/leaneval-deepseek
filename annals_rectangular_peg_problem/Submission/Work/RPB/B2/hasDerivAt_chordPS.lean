import Mathlib
import Submission.Work.RPV.Defs

open Complex

namespace Work.RPB.B2

/-- The real part of a complex-valued differentiable function is differentiable,
with derivative the real part of the complex derivative. -/
private lemma hasDerivAt_re {F : ℝ → ℂ} {t : ℝ} {d : ℂ} (h : HasDerivAt F d t) :
    HasDerivAt (fun s => (F s).re) d.re t := by
  have h1 : HasDerivAt (fun s => Complex.reCLM (F s)) (Complex.reCLM d) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  convert h1 using 1
  · ext s; exact Complex.reCLM_apply _
  · exact (Complex.reCLM_apply d).symm

/-- The imaginary part of a complex-valued differentiable function is differentiable,
with derivative the imaginary part of the complex derivative. -/
private lemma hasDerivAt_im {F : ℝ → ℂ} {t : ℝ} {d : ℂ} (h : HasDerivAt F d t) :
    HasDerivAt (fun s => (F s).im) d.im t := by
  have h1 : HasDerivAt (fun s => Complex.imCLM (F s)) (Complex.imCLM d) t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
  convert h1 using 1
  · ext s; exact Complex.imCLM_apply _
  · exact (Complex.imCLM_apply d).symm

/-- Derivative of `s ↦ ‖z s‖ ^ 2`, in terms of the real inner product on `ℂ`. -/
private lemma hasDerivAt_normSq {z : ℝ → ℂ} {t : ℝ} {ζ : ℂ} (hz : HasDerivAt z ζ t) :
    HasDerivAt (fun s => ‖z s‖ ^ 2) (2 * ((starRingEnd ℂ) (z t) * ζ).re) t := by
  convert hz.norm_sq using 1
  rw [Complex.inner]
  simp [mul_comm]

theorem hasDerivAt_chordPS {z w : ℝ → ℂ} {A : ℝ → ℝ} {t A' : ℝ} {ζ η : ℂ}
    (hz : HasDerivAt z ζ t) (hw : HasDerivAt w η t) (hA : HasDerivAt A A' t)
    (hA' : A' = ((ζ - η) / (z t - w t)).im) :
    HasDerivAt (fun s => Work.RPV.chordPS (z s) (w s) (A s))
      (Work.RPV.dchord (z t) (w t) (A t) ζ η) t := by
  set du : ℂ := Complex.exp (-(A t : ℂ) * I) *
      ((ζ + η) / (Real.sqrt 2 : ℂ) -
        ((A' : ℂ) * I) * ((z t + w t) / (Real.sqrt 2 : ℂ))) with hdu
  set e : ℝ := ((starRingEnd ℂ) (z t) * ζ).re + ((starRingEnd ℂ) (w t) * η).re with he
  have hAc : HasDerivAt (fun s => (A s : ℂ)) (A' : ℂ) t := hA.ofReal_comp
  have hg : HasDerivAt
      (fun s => Complex.exp (-(A s : ℂ) * I) * ((z s + w s) / (Real.sqrt 2 : ℂ))) du t := by
    have ha : HasDerivAt (fun s => -(A s : ℂ) * I) (-(A' : ℂ) * I) t :=
      hAc.neg.mul_const I
    have hexp : HasDerivAt (fun s => Complex.exp (-(A s : ℂ) * I))
        (Complex.exp (-(A t : ℂ) * I) * (-(A' : ℂ) * I)) t :=
      (Complex.hasDerivAt_exp (-(A t : ℂ) * I)).comp t ha
    have hu : HasDerivAt (fun s => (z s + w s) / (Real.sqrt 2 : ℂ))
        ((ζ + η) / (Real.sqrt 2 : ℂ)) t := (hz.add hw).div_const _
    refine (hexp.mul hu).congr_deriv ?_
    rw [hdu]; ring
  have hq1 : HasDerivAt
      (fun s => (Complex.exp (-(A s : ℂ) * I) * ((z s + w s) / (Real.sqrt 2 : ℂ))).im)
      du.im t :=
    hasDerivAt_im hg
  have hp1 : HasDerivAt
      (fun s => (Complex.exp (-(A s : ℂ) * I) * ((z s + w s) / (Real.sqrt 2 : ℂ))).re)
      du.re t :=
    hasDerivAt_re hg
  have hp2 : HasDerivAt (fun s => (‖z s‖ ^ 2 + ‖w s‖ ^ 2) / 2 - 1) e t := by
    have hz2 := hasDerivAt_normSq hz
    have hw2 := hasDerivAt_normSq hw
    have hhalf : HasDerivAt (fun s => (‖z s‖ ^ 2 + ‖w s‖ ^ 2) / 2)
        ((2 * ((starRingEnd ℂ) (z t) * ζ).re + 2 * ((starRingEnd ℂ) (w t) * η).re) / 2)
        t :=
      (hz2.add hw2).div_const 2
    refine (hhalf.sub_const 1).congr_deriv ?_
    rw [he]; ring
  have hfull : HasDerivAt (fun s => Work.RPV.chordPS (z s) (w s) (A s))
      (((du.im, A'), (du.re, e))) t :=
    (hq1.prodMk hA).prodMk (hp1.prodMk hp2)
  have hdchord : (((du.im, A'), (du.re, e))) = Work.RPV.dchord (z t) (w t) (A t) ζ η := by
    simp only [Work.RPV.dchord]
    rw [← hA', ← hdu, ← he]
  rwa [hdchord] at hfull

end Work.RPB.B2
