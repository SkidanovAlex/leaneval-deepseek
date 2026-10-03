import Mathlib

namespace Work.FIArea7

/-- Integration by parts for the Fourier-type kernel `x ↦ exp(-(I * ℓ * x))` with `ℓ ≠ 0`:
the integral of `f` against the kernel equals `(I * ℓ)⁻¹` times the integral of `deriv f`
against the kernel. -/
theorem integral_mul_cexp_eq (f : ℝ → ℂ) (ℓ : ℤ)
    (hdiff : Differentiable ℝ f) (hdcont : Continuous (deriv f))
    (hsupp : HasCompactSupport f) (hℓ : (ℓ : ℂ) ≠ 0) :
    ∫ x, f x * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ)))
      = (Complex.I * (ℓ : ℂ))⁻¹ * ∫ x, deriv f x * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ))) := by
  have hvcont : Continuous (fun x : ℝ => Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ)))) := by
    fun_prop
  have hv'cont : Continuous (fun x : ℝ => (-(Complex.I * (ℓ : ℂ))) * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ)))) := by
    fun_prop
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-(Complex.I * (ℓ : ℂ) * (y : ℂ))))
      ((-(Complex.I * (ℓ : ℂ))) * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ)))) x := by
    intro x
    have hbase : HasDerivAt (fun z : ℂ => Complex.exp (-(Complex.I * (ℓ : ℂ) * z)))
        (Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ))) * (-(Complex.I * (ℓ : ℂ)))) (x : ℂ) := by
      have hp : HasDerivAt (fun z : ℂ => (Complex.I * (ℓ : ℂ)) * z) (Complex.I * (ℓ : ℂ)) (x : ℂ) :=
        hasDerivAt_const_mul (x := (x : ℂ)) (Complex.I * (ℓ : ℂ))
      exact (hp.neg).cexp
    have hcomp := hbase.comp_ofReal
    convert hcomp using 1
    ring
  have key := MeasureTheory.integral_mul_deriv_eq_deriv_mul (A := ℂ) (a' := 0) (b' := 0)
    (u := f) (v := fun x : ℝ => Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ))))
    (u' := deriv f)
    (v' := fun x : ℝ => (-(Complex.I * (ℓ : ℂ))) * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ))))
    (fun x _ => (hdiff x).hasDerivAt)
    (fun x _ => hderiv x)
    ((hdiff.continuous.mul hv'cont).integrable_of_hasCompactSupport hsupp.mul_right)
    ((hdcont.mul hvcont).integrable_of_hasCompactSupport hsupp.deriv.mul_right)
    ((hsupp.mul_right.is_zero_at_infty).mono_left atBot_le_cocompact)
    ((hsupp.mul_right.is_zero_at_infty).mono_left atTop_le_cocompact)
  simp only [sub_zero, zero_sub] at key
  have hconst : ∫ x, f x * ((-(Complex.I * (ℓ : ℂ))) * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ))))
      = (-(Complex.I * (ℓ : ℂ))) * ∫ x, f x * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ))) := by
    have hfun : (fun x : ℝ => f x * ((-(Complex.I * (ℓ : ℂ))) * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ)))))
        = (fun x : ℝ => (-(Complex.I * (ℓ : ℂ))) * (f x * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ))))) := by
      funext x; ring
    rw [hfun, MeasureTheory.integral_const_mul]
  have hfinal : (Complex.I * (ℓ : ℂ)) * ∫ x, f x * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ)))
      = ∫ x, deriv f x * Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ))) := by
    have h := key
    rw [hconst] at h
    rw [neg_mul] at h
    exact neg_injective h
  rw [← hfinal, inv_mul_cancel_left₀ (mul_ne_zero Complex.I_ne_zero hℓ)]

end Work.FIArea7
