/-
# Puig's argument (C12): the dual recurrence for the Fourier coefficients

If `u : ℝ → ℂ` is continuous and `1`-periodic and solves the **dual** (frequency `1`)
almost Mathieu equation

`u (x + α) + u (x - α) = (E - 2 λ cos 2π x) u x`,

then its Fourier coefficients `cF u n = ∫₀¹ e^{-2πi n x} u x dx` satisfy the **original**
almost Mathieu recurrence

`λ (cF u (n+1) + cF u (n-1)) = (E - 2 cos (2π n α)) cF u n`.

This is proved purely from the shift/multiplication rules for `cF` established in
`FourierAux` (no Fourier inversion is needed): take the `n`-th Fourier coefficient of both
sides of the dual equation, use `cF_shift` on the left and `two_mul_cos_eq` together with
`cF_chr_mul` on the right.
-/
import Mathlib
import Submission.Work.TMPuig.FourierAux

open MeasureTheory intervalIntegral
open scoped Real

noncomputable section

namespace Work.TMPuig

/-! ## Helpers on characters and Fourier coefficients -/

/-- `chr k (-a) = chr (-k) a`: shifting the argument back by `a` negates the index. -/
theorem chr_neg_arg (k : ℤ) (a : ℝ) : chr k (-a) = chr (-k) a := by
  rw [chr, chr]; congr 1; push_cast; ring

/-- `chr k a + chr (-k) a = 2 cos (2π k a)` (a real number, coerced). -/
theorem chr_add_neg_eq_two_cos (k : ℤ) (a : ℝ) :
    chr k a + chr (-k) a = ((2 * Real.cos (2 * Real.pi * (k:ℝ) * a) : ℝ) : ℂ) := by
  have h1 : chr k a = Complex.cos ((2 * Real.pi * (k:ℝ) * a : ℝ) : ℂ)
      + Complex.sin ((2 * Real.pi * (k:ℝ) * a : ℝ) : ℂ) * Complex.I := by
    rw [chr, show (2 * Real.pi * Complex.I * ((k : ℤ) : ℝ) * a)
        = ((2 * Real.pi * (k:ℝ) * a : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I]
  have h2 : chr (-k) a = Complex.cos ((2 * Real.pi * (k:ℝ) * a : ℝ) : ℂ)
      - Complex.sin ((2 * Real.pi * (k:ℝ) * a : ℝ) : ℂ) * Complex.I := by
    rw [chr, show (2 * Real.pi * Complex.I * (((-k : ℤ)) : ℝ) * a)
        = (-(((2 * Real.pi * (k:ℝ) * a : ℝ)) : ℂ)) * Complex.I by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2, ← Complex.ofReal_cos]
  push_cast
  ring

/-- Shifting the argument by `-a` multiplies the `n`-th coefficient by `e^{-2πi n a}`. -/
theorem cF_shift_sub (f : ℝ → ℂ) (hfp : ∀ x, f (x + 1) = f x) (a : ℝ) (n : ℤ) :
    cF (fun x => f (x - a)) n = chr (-n) a * cF f n := by
  have h : (fun x => f (x - a)) = (fun x => f (x + (-a))) := by funext x; ring_nf
  rw [h, cF_shift f hfp (-a) n, chr_neg_arg]

/-- Linearity of the Fourier coefficient in the function (subtraction). -/
theorem cF_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    cF (fun x => f x - g x) n = cF f n - cF g n := by
  rw [cF, cF, cF]
  rw [show (∫ x in (0:ℝ)..1, chr (-n) x * (f x - g x))
      = ∫ x in (0:ℝ)..1, (chr (-n) x * f x - chr (-n) x * g x) from by
        apply intervalIntegral.integral_congr; intro x _; ring]
  rw [intervalIntegral.integral_sub]
  · exact (((continuous_chr (-n)).mul hf).intervalIntegrable 0 1)
  · exact (((continuous_chr (-n)).mul hg).intervalIntegrable 0 1)

/-- Multiplication by `2 cos 2πx = chr 1 x + chr (-1) x` shifts the index by `±1`. -/
theorem cF_two_cos_mul (f : ℝ → ℂ) (hf : Continuous f) (n : ℤ) :
    cF (fun x => ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * f x) n =
      cF f (n - 1) + cF f (n + 1) := by
  have hcongr : (fun x => ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * f x) =
      (fun x => chr 1 x * f x + chr (-1) x * f x) := by
    funext x
    rw [two_mul_cos_eq]
    ring
  have h1 : cF (fun x => chr 1 x * f x) n = cF f (n - 1) := cF_chr_mul f 1 n
  have h2 : cF (fun x => chr (-1) x * f x) n = cF f (n + 1) := by
    rw [cF_chr_mul f (-1) n]
    congr 1
  have hadd : cF (fun x => chr 1 x * f x + chr (-1) x * f x) n
      = cF (fun x => chr 1 x * f x) n + cF (fun x => chr (-1) x * f x) n :=
    cF_add ((continuous_chr 1).mul hf) ((continuous_chr (-1)).mul hf) n
  rw [hcongr, hadd, h1, h2]

/-! ## The dual recurrence -/

theorem dual_recurrence {α lam E : ℝ} {u : ℝ → ℂ} (hu : Continuous u)
    (hup : ∀ x, u (x + 1) = u x)
    (huq : ∀ x, u (x + α) + u (x - α) =
      ((E - 2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * u x)
    (n : ℤ) :
    (lam : ℂ) * (cF u (n + 1) + cF u (n - 1)) =
      ((E : ℂ) - ((2 * Real.cos (2 * Real.pi * (n : ℝ) * α) : ℝ) : ℂ)) * cF u n := by
  -- the `n`-th Fourier coefficients of the two sides of the dual equation agree
  have key := cF_congr huq n
  -- left side: `cF (u(·+α) + u(·-α)) n = 2 cos (2π n α) · cF u n`
  have hL : cF (fun x => u (x + α) + u (x - α)) n =
      ((2 * Real.cos (2 * Real.pi * (n:ℝ) * α) : ℝ) : ℂ) * cF u n := by
    have hA : cF (fun x => u (x + α)) n = chr n α * cF u n := cF_shift u hup α n
    have hB : cF (fun x => u (x - α)) n = chr (-n) α * cF u n := cF_shift_sub u hup α n
    have hadd : cF (fun x => u (x + α) + u (x - α)) n
        = cF (fun x => u (x + α)) n + cF (fun x => u (x - α)) n :=
      cF_add (hu.comp (continuous_id.add continuous_const))
             (hu.comp (continuous_id.sub continuous_const)) n
    rw [hadd, hA, hB, ← add_mul, chr_add_neg_eq_two_cos]
  -- the potential term: `cF (2 λ cos 2πx · u) n = λ (cF u (n-1) + cF u (n+1))`
  have hG : cF (fun x => ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * u x) n
      = (lam : ℂ) * (cF u (n - 1) + cF u (n + 1)) := by
    have hcongr2 : (fun x => ((2*lam*Real.cos (2*Real.pi*x):ℝ):ℂ) * u x) =
        (fun x => (lam:ℂ) * (((2*Real.cos (2*Real.pi*x):ℝ):ℂ) * u x)) := by
      funext x
      have hcoef : ((2*lam*Real.cos (2*Real.pi*x):ℝ):ℂ)
          = (lam:ℂ) * ((2*Real.cos (2*Real.pi*x):ℝ):ℂ) := by push_cast; ring
      rw [hcoef]; ring
    rw [hcongr2, cF_const_mul, cF_two_cos_mul u hu n]
  -- right side: `cF ((E - 2λ cos 2πx) · u) n = E · cF u n - λ (cF u (n-1) + cF u (n+1))`
  have hR : cF (fun x => ((E - 2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * u x) n =
      (E : ℂ) * cF u n - (lam : ℂ) * (cF u (n - 1) + cF u (n + 1)) := by
    have hcongr1 : (fun x => ((E - 2*lam*Real.cos (2*Real.pi*x):ℝ):ℂ) * u x) =
        (fun x => (E:ℂ) * u x - (((2*lam*Real.cos (2*Real.pi*x):ℝ):ℂ) * u x)) := by
      funext x
      rw [Complex.ofReal_sub]
      ring
    have hsub : cF (fun x => (E:ℂ) * u x
          - (((2*lam*Real.cos (2*Real.pi*x):ℝ):ℂ) * u x)) n
        = cF (fun x => (E:ℂ) * u x) n
          - cF (fun x => (((2*lam*Real.cos (2*Real.pi*x):ℝ):ℂ) * u x)) n :=
      cF_sub (by fun_prop) (by fun_prop) n
    rw [hcongr1, hsub, cF_const_mul, hG]
  -- combine
  have hkey : ((2 * Real.cos (2 * Real.pi * (n:ℝ) * α) : ℝ) : ℂ) * cF u n
      = (E : ℂ) * cF u n - (lam : ℂ) * (cF u (n - 1) + cF u (n + 1)) := by
    rw [← hL, ← hR]; exact key
  have h2 : (E : ℂ) * cF u n - ((2 * Real.cos (2 * Real.pi * (n:ℝ) * α) : ℝ) : ℂ) * cF u n
      = (lam : ℂ) * (cF u (n - 1) + cF u (n + 1)) := by
    rw [hkey]; ring
  rw [add_comm (cF u (n + 1)) (cF u (n - 1)), ← h2, ← sub_mul]

end Work.TMPuig
