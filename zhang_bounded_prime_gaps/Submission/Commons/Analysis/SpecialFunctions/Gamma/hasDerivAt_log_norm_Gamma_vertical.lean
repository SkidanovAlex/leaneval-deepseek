import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

open Complex
open scoped RealInnerProductSpace

namespace Commons.Analysis.SpecialFunctions.Gamma

private lemma hasDerivAt_log_norm {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log ‖f y‖) ((f' / f x).re) x := by
  have hsq : HasDerivAt (fun y => ‖f y‖ ^ 2) (2 * inner ℝ (f x) f') x := hf.norm_sq
  have hpos : (0 : ℝ) < ‖f x‖ := norm_pos_iff.mpr hx
  have hne : ‖f x‖ ^ 2 ≠ 0 := by positivity
  have hlog : HasDerivAt (fun y => Real.log (‖f y‖ ^ 2))
      ((2 * inner ℝ (f x) f') / ‖f x‖ ^ 2) x := hsq.log hne
  have hhalf : HasDerivAt (fun y => (1/2 : ℝ) * Real.log (‖f y‖ ^ 2))
      ((1/2 : ℝ) * ((2 * inner ℝ (f x) f') / ‖f x‖ ^ 2)) x := hlog.const_mul (1/2)
  have hfun : (fun y => (1/2 : ℝ) * Real.log (‖f y‖ ^ 2)) = fun y => Real.log ‖f y‖ := by
    funext y
    rw [Real.log_pow]
    ring
  rw [hfun] at hhalf
  have hinner : inner ℝ (f x) f' = f'.re * (f x).re + f'.im * (f x).im := by
    rw [Complex.inner]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hdiv : (f' / f x).re = (f'.re * (f x).re + f'.im * (f x).im) / ‖f x‖ ^ 2 := by
    rw [Complex.div_re, Complex.normSq_eq_norm_sq]
    ring
  convert hhalf using 1
  rw [hinner, hdiv]
  field_simp

private lemma hasDerivAt_Gamma_vertical (u v : ℝ) (hu : 0 < u) :
    HasDerivAt (fun y : ℝ => Complex.Gamma ((u : ℂ) + (y : ℂ) * Complex.I))
      (Complex.I * deriv Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)) v := by
  have hφ : HasDerivAt (fun y : ℝ => (u : ℂ) + (y : ℂ) * Complex.I) Complex.I v := by
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) v := by
      simpa using (hasDerivAt_id v).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) (Complex.I) v := by
      simpa using h1.mul_const Complex.I
    simpa using h2.const_add (u : ℂ)
  have hs : ∀ m : ℕ, ((u : ℂ) + (v : ℂ) * Complex.I) ≠ -↑m := by
    intro m hm
    have hre : ((u : ℂ) + (v : ℂ) * Complex.I).re = (-↑m : ℂ).re := by rw [hm]
    simp at hre
    have hmnn : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I))
      ((u : ℂ) + (v : ℂ) * Complex.I) :=
    (Complex.differentiableAt_Gamma _ hs).hasDerivAt
  have hc := hΓ.scomp v hφ
  simpa [Function.comp_def, smul_eq_mul] using hc

theorem hasDerivAt_log_norm_Gamma_vertical (u v : ℝ) (hu : 0 < u) :
    HasDerivAt (fun y : ℝ => Real.log ‖Complex.Gamma ((u : ℂ) + (y : ℂ) * Complex.I)‖)
      (-(Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I)).im) v := by
  set z : ℂ := (u : ℂ) + (v : ℂ) * Complex.I with hz
  have hzre : z.re = u := by simp [hz]
  have hpos : 0 < z.re := by rw [hzre]; exact hu
  have hGnz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hpos
  have hderiv : deriv Complex.Gamma z = Complex.Gamma z * Complex.digamma z := by
    have hdef : Complex.digamma z = deriv Complex.Gamma z / Complex.Gamma z := by
      rw [Complex.digamma_def, logDeriv_apply]
    rw [hdef]
    field_simp
  have hg : HasDerivAt (fun y : ℝ => Complex.Gamma ((u : ℂ) + (y : ℂ) * Complex.I))
      (Complex.I * (Complex.Gamma z * Complex.digamma z)) v := by
    have h := hasDerivAt_Gamma_vertical u v hu
    rw [← hz] at h
    rw [hderiv] at h
    exact h
  have hres := hasDerivAt_log_norm hg hGnz
  have hval : ((Complex.I * (Complex.Gamma z * Complex.digamma z)) / Complex.Gamma z).re
      = -(Complex.digamma z).im := by
    rw [show (Complex.I * (Complex.Gamma z * Complex.digamma z)) / Complex.Gamma z
        = Complex.I * Complex.digamma z by
          field_simp]
    simp [Complex.mul_re]
  rw [hval] at hres
  simpa [z] using hres

end Commons.Analysis.SpecialFunctions.Gamma