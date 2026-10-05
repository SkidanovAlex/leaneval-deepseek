import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPB.B5.area_normalised

/-!
# `signedArea_circle_scaled`: the signed area of a scaled, rotated circle

For every real radius `R` and every phase `ψ` the circle
`t ↦ (R : ℂ) · exp ((t + ψ) · I)`
has signed area `R ^ 2 · π`.

Two facts produce this.

* **Real scaling.**  `signedArea_const_mul` (in `Submission.Work.RPB.B5.area_normalised`) turns the
  real factor `R` into the square `R ^ 2`, reducing to the unit circle
  `t ↦ exp ((t + ψ) · I)`.

* **Pointwise computation.**  The exponential is differentiable everywhere, so
  `deriv (t ↦ exp ((t + ψ) · I)) t = exp ((t + ψ) · I) · I`.  Since
  `conj z · z = ↑(normSq z)` and `normSq (exp (x · I)) = 1`, the area integrand
  `ω_ℂ e (e · I) = (conj e · (e · I)).im = (conj e · e).re = normSq e` is identically `1`.
  Integrating `1` over a period gives `2π`, and the factor `1/2` in `signedArea` gives `π`.

The phase `ψ` is irrelevant to the value: it only rotates the curve, which the modulus-`1`
computation absorbs.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

open Work.RPV

/-- **Derivative of a phase-shifted unit-circle parametrisation.**
`deriv (t ↦ exp ((t + ψ) · I)) t = exp ((t + ψ) · I) · I`. -/
private lemma deriv_exp_shift (ψ t : ℝ) :
    deriv (fun s : ℝ => Complex.exp (((s : ℂ) + (ψ : ℂ)) * Complex.I)) t
      = Complex.exp (((t : ℂ) + (ψ : ℂ)) * Complex.I) * Complex.I := by
  have hinner : HasDerivAt (fun s : ℝ => ((s : ℂ) + (ψ : ℂ)) * Complex.I) (Complex.I) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) + (ψ : ℂ)) (1 : ℂ) t := h1.add_const _
    simpa using h2.mul_const Complex.I
  have h3 : HasDerivAt (fun s : ℝ => Complex.exp (((s : ℂ) + (ψ : ℂ)) * Complex.I))
      (Complex.I • Complex.exp (((t : ℂ) + (ψ : ℂ)) * Complex.I)) t :=
    (Complex.hasDerivAt_exp _).scomp t hinner
  rw [h3.deriv]
  simp [smul_eq_mul, mul_comm]

/-- **The unit-modulus computation.**  `conj e · e = ↑(normSq e)` is real of modulus `1`, so
`ω_ℂ e (e · I) = 1` for `e = exp (a · I)`. -/
private lemma omegaC_exp_ofReal_mul_I_re (a : ℝ) :
    Work.RPV.ωC (Complex.exp ((a : ℂ) * Complex.I))
      (Complex.exp ((a : ℂ) * Complex.I) * Complex.I) = 1 := by
  have hns : Complex.normSq (Complex.exp ((a : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    rw [show ‖Complex.exp ((a : ℂ) * Complex.I)‖ = 1 from Complex.norm_exp_ofReal_mul_I a]
    norm_num
  simp only [Work.RPV.ωC]
  rw [← mul_assoc, Complex.mul_I_im]
  rw [show (starRingEnd ℂ) (Complex.exp ((a : ℂ) * Complex.I)) *
      Complex.exp ((a : ℂ) * Complex.I) = ((Complex.normSq _ : ℝ) : ℂ) from ?_]
  · rw [Complex.ofReal_re, hns]
  · rw [Complex.normSq_eq_conj_mul_self]

/-- **Signed area of the phase-shifted unit circle.**
`Work.RPB.signedArea (t ↦ exp ((t + ψ) · I)) = π` for every real `ψ`. -/
private lemma signedArea_circle_unit (ψ : ℝ) :
    Work.RPB.signedArea (fun t : ℝ => Complex.exp ((t + ψ) * Complex.I)) = Real.pi := by
  have hpoint : ∀ t : ℝ, Work.RPV.ωC (Complex.exp (((t : ℂ) + (ψ : ℂ)) * Complex.I))
      (deriv (fun s : ℝ => Complex.exp (((s : ℂ) + (ψ : ℂ)) * Complex.I)) t) = 1 := by
    intro t
    rw [deriv_exp_shift ψ t]
    have h : ((t : ℂ) + (ψ : ℂ)) = ((t + ψ : ℝ) : ℂ) := by push_cast; ring
    rw [h]
    exact omegaC_exp_ofReal_mul_I_re (t + ψ)
  rw [Work.RPB.signedArea]
  have hcongr : (∫ t in (0 : ℝ)..(2 * Real.pi),
        Work.RPV.ωC (Complex.exp (((t : ℂ) + (ψ : ℂ)) * Complex.I))
          (deriv (fun s : ℝ => Complex.exp (((s : ℂ) + (ψ : ℂ)) * Complex.I)) t))
      = ∫ t in (0 : ℝ)..(2 * Real.pi), (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact hpoint t
  rw [hcongr, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem signedArea_circle_scaled (R ψ : ℝ) :
    Work.RPB.signedArea (fun t : ℝ => (R : ℂ) * Complex.exp ((t + ψ) * Complex.I))
      = R ^ 2 * Real.pi := by
  rw [signedArea_const_mul (fun t : ℝ => Complex.exp ((t + ψ) * Complex.I)) R,
    signedArea_circle_unit ψ]

end Work.RPB.B5
