import Mathlib
import Submission.Work.TMContract.Defs

/-!
# C11: Fourier-coefficient calculus for 1-periodic functions

Small self-contained API around `fourierCoeffOn` on `[0,1]`, in the normalisation
`φ̂ k = ∫₀¹ φ x * exp (-(2πi k x)) dx`, together with the translation rule
`(x ↦ f (x + α))^k = exp (2πi k α) * f̂ k` used in component C11 (AJ (4.18), (4.22)).
-/

open MeasureTheory intervalIntegral

set_option autoImplicit false

noncomputable section

namespace Work.TMComp.RedProj

/-- The exponential kernel `exp (-(2πi k x))`. -/
def ek (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℝ) : ℂ)))

theorem ek_periodic (k : ℤ) (x : ℝ) : ek k (x + 1) = ek k x := by
  simp only [ek]
  have hcast : (((x + 1 : ℝ)) : ℂ) = (x : ℂ) + 1 := by push_cast; ring
  rw [hcast,
    show -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((x : ℂ) + 1))
      = -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ))
        + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The kernel has modulus one. -/
theorem norm_ek (k : ℤ) (x : ℝ) : ‖ek k x‖ = 1 := by
  rw [ek, show -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ))
      = ((-(2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The Fourier coefficient of a function on `[0,1]` as an exponential integral. -/
theorem fcoef_eq_int (f : ℝ → ℂ) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f k = ∫ x in (0 : ℝ)..1, f x * ek k x := by
  rw [fourierCoeffOn_eq_integral f k (show (0 : ℝ) < 1 by norm_num)]
  simp only [sub_zero, div_one, one_smul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [smul_eq_mul, fourier_coe_apply, ek]
  have hden : (((1 : ℝ) - 0 : ℝ) : ℂ) = 1 := by norm_num
  rw [hden, div_one]
  have h : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (↑(-k) : ℂ) * (x : ℂ))
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [h]
  ring

/-- The monomial kernel has mean zero on a period. -/
theorem integral_ek_zero (k : ℤ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..1, ek k x) = 0 := by
  have hc : -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) ≠ 0 := by
    rw [neg_ne_zero, mul_ne_zero_iff, mul_ne_zero_iff]
    refine ⟨⟨?_, Complex.I_ne_zero⟩, ?_⟩
    · exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos))
    · exact_mod_cast hk
  have hcong : (∫ x in (0 : ℝ)..1, ek k x)
      = ∫ x in (0 : ℝ)..1,
          Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))) * (x : ℂ)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [ek]
    congr 1
    ring
  rw [hcong, integral_exp_mul_complex (a := (0 : ℝ)) (b := (1 : ℝ)) hc,
    show -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * ((1 : ℝ) : ℂ)
      = (-k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
    show -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * ((0 : ℝ) : ℂ) = 0 by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_zero, sub_self, zero_div]

/-- `ek k` is the exponential of a multiple of `x`. -/
theorem ek_eq_exp_mul (k : ℤ) :
    ek k = fun x : ℝ =>
      Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))) * (x : ℂ)) := by
  funext x
  simp only [ek]
  congr 1
  ring

/-- **Translation rule.** For a 1-periodic `f`, the `k`-th coefficient of `x ↦ f (x + α)`
is `exp (2πi k α)` times that of `f`. -/
theorem fcoef_shift (f : ℝ → ℂ) (hf : ∀ x, f (x + 1) = f x) (α : ℝ) (k : ℤ) :
    fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => f (x + α)) k
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ))
        * fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f k := by
  rw [fcoef_eq_int (fun x => f (x + α)) k, fcoef_eq_int f k]
  have hper : Function.Periodic (fun y : ℝ => f y * ek k y) 1 := by
    intro y
    show f (y + 1) * ek k (y + 1) = f y * ek k y
    rw [hf y, ek_periodic k y]
  have hL : (∫ x in (0 : ℝ)..1, f (x + α) * ek k x)
      = ∫ y in α..α + 1, f y * ek k (y - α) := by
    have h1 : (∫ x in (0 : ℝ)..1, f (x + α) * ek k x)
        = ∫ x in (0 : ℝ)..1, (fun y : ℝ => f y * ek k (y - α)) (x + α) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp
    rw [h1, intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun y : ℝ => f y * ek k (y - α)) α]
    rw [zero_add, add_comm 1 α]
  have h2 : ∀ y : ℝ, ek k (y - α)
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) * ek k y := by
    intro y
    have hcast : (((y - α : ℝ)) : ℂ) = (y : ℂ) - (α : ℂ) := by push_cast; ring
    simp only [ek, hcast]
    rw [show -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((y : ℂ) - (α : ℂ)))
        = 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)
          + -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (y : ℂ)) by ring,
      Complex.exp_add]
  rw [hL]
  have h3 : (∫ y in α..α + 1, f y * ek k (y - α))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ))
        * ∫ y in α..α + 1, f y * ek k y := by
    rw [show (∫ y in α..α + 1, f y * ek k (y - α))
        = ∫ y in α..α + 1,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ))
              * (f y * ek k y) from by
          refine intervalIntegral.integral_congr fun y _ => ?_
          rw [h2 y]; ring]
    rw [intervalIntegral.integral_const_mul]
  rw [h3]
  congr 1
  simpa using hper.intervalIntegral_add_eq α 0

end Work.TMComp.RedProj
