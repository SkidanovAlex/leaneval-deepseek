import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

noncomputable section

open Complex

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- Auxiliary: the logarithmic derivative of `z ↦ c ^ (a * z)` at a point where `c ≠ 0`. -/
lemma logDeriv_const_cpow_const_mul (c a z : ℂ) (hc : c ≠ 0) :
    logDeriv (fun w : ℂ => c ^ (a * w)) z = a * Complex.log c := by
  have hc' : c ^ (a * z) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hc)
  have hf : DifferentiableAt ℂ (fun y : ℂ => c ^ y) (a * z) :=
    (Complex.hasStrictDerivAt_const_cpow (x := c) (y := a * z) (Or.inl hc)).hasDerivAt.differentiableAt
  have hg : DifferentiableAt ℂ (fun w : ℂ => a * w) z := by fun_prop
  have hcomp : logDeriv (fun w : ℂ => c ^ (a * w)) z
      = logDeriv (fun y : ℂ => c ^ y) (a * z) * deriv (fun w : ℂ => a * w) z := by
    rw [show (fun w : ℂ => c ^ (a * w))
        = ((fun y : ℂ => c ^ y) ∘ (fun w : ℂ => a * w)) from rfl]
    exact logDeriv_comp hf hg
  rw [hcomp, logDeriv_apply,
    (Complex.hasStrictDerivAt_const_cpow (x := c) (y := a * z) (Or.inl hc)).hasDerivAt.deriv]
  have hder2 : deriv (fun w : ℂ => a * w) z = a := by simp
  rw [hder2]
  field_simp

theorem logDeriv_GammaR_off_pole (z : ℂ) (hz : ∀ m : ℕ, z / 2 ≠ -(m : ℂ)) :
    logDeriv Complex.Gammaℝ z = -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (z / 2) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hGam : Complex.Gamma (z / 2) ≠ 0 := Complex.Gamma_ne_zero hz
  have hfun : Complex.Gammaℝ
      = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
    funext w
    rw [Complex.Gammaℝ_def]
  rw [hfun]
  have hc_ne : (Real.pi : ℂ) ^ (-z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hf : DifferentiableAt ℂ (fun y : ℂ => (Real.pi : ℂ) ^ y) (-z / 2) :=
    (Complex.hasStrictDerivAt_const_cpow (x := (Real.pi : ℂ)) (y := -z / 2)
      (Or.inl hpi)).hasDerivAt.differentiableAt
  have hd_f : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z := by
    have hg : DifferentiableAt ℂ (fun w : ℂ => -w / 2) z := by fun_prop
    exact hf.comp z hg
  have hd_g : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z :=
    (Complex.differentiableAt_Gamma (z / 2) hz).comp z (by fun_prop)
  erw [logDeriv_mul z hc_ne hGam hd_f hd_g]
  have h1 : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z
      = -(Complex.log (Real.pi : ℂ)) / 2 := by
    rw [show (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
        = (fun w : ℂ => (Real.pi : ℂ) ^ ((-(1 / 2)) * w)) from by
      funext w; ring_nf]
    rw [logDeriv_const_cpow_const_mul (Real.pi : ℂ) (-(1 / 2)) z hpi]
    ring
  have h2 : logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) z
      = Complex.digamma (z / 2) / 2 := by
    have hfg : DifferentiableAt ℂ Complex.Gamma (z / 2) :=
      Complex.differentiableAt_Gamma (z / 2) hz
    have hgg : DifferentiableAt ℂ (fun w : ℂ => w / 2) z := by fun_prop
    have hcomp : logDeriv (fun w : ℂ => Complex.Gamma (w / 2)) z
        = logDeriv Complex.Gamma (z / 2) * deriv (fun w : ℂ => w / 2) z := by
      rw [show (fun w : ℂ => Complex.Gamma (w / 2))
          = (Complex.Gamma ∘ (fun w : ℂ => w / 2)) from rfl]
      exact logDeriv_comp hfg hgg
    rw [hcomp]
    have hd : deriv (fun w : ℂ => w / 2) z = 1 / 2 := by simp
    rw [hd]
    have hdig : logDeriv Complex.Gamma (z / 2) = Complex.digamma (z / 2) := rfl
    rw [hdig]
    ring
  rw [h1, h2]

end Commons.Analysis.SpecialFunctions.Gamma