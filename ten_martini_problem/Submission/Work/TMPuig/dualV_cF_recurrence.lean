/-
# Puig's argument (C12): the recurrence for the Fourier coefficients of `dualV`

`dualV B` is the `1`-periodic Bloch function attached to the reducibility datum `B`; it
solves the dual ("Bloch") almost Mathieu equation with a *twisted* frequency term

`e^{2πic} V (x+α) + e^{-2πic} V (x-α) + 2λ cos(2πx) V x = E V x`.

Taking the `n`-th Fourier coefficient and using the shift/multiplication rules for `cF`
(`cF_shift`, `cF_shift_sub`, `cF_chr_mul`) turns the shifts into the characters
`e^{2πi n α}` and `e^{-2πi n α}`, which combine with `e^{±2πic}` into `2 cos (2π(nα + c))`.
This is the recurrence solved by the `ℓ²` sequence of the dual operator.
-/
import Mathlib
import Submission.Work.TMPuig.DualDefs
import Submission.Work.TMPuig.FourierAux
import Submission.Work.TMPuig.dual_recurrence

open MeasureTheory intervalIntegral
open scoped Real

noncomputable section

namespace Work.TMPuig

/-- The character twist: `dualE c * chr n α + (dualE c)⁻¹ * chr n (-α) = 2 cos (2π (n α + c))`. -/
theorem dualE_chr_cos (c : ℝ) (n : ℤ) (α : ℝ) :
    dualE c * chr n α + (dualE c)⁻¹ * chr n (-α)
      = ((2 * Real.cos (2 * Real.pi * ((n : ℝ) * α + c)) : ℝ) : ℂ) := by
  set R : ℝ := 2 * Real.pi * ((n : ℝ) * α + c) with hR
  have h1 : dualE c * chr n α = Complex.exp ((R : ℂ) * Complex.I) := by
    rw [dualE, chr, ← Complex.exp_add]
    congr 1
    rw [hR]; push_cast; ring
  have h2 : (dualE c)⁻¹ * chr n (-α) = Complex.exp (-((R : ℂ) * Complex.I)) := by
    rw [dualE, chr, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    rw [hR]; push_cast; ring
  have h2' : Complex.exp (-((R : ℂ) * Complex.I))
      = Complex.cos (R : ℂ) - Complex.sin (R : ℂ) * Complex.I := by
    rw [show -((R : ℂ) * Complex.I) = (-(R : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2, h2', Complex.exp_mul_I, hR, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

theorem dualV_cF_recurrence {α lam E c : ℝ} {B : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hcont : Continuous (dualV B)) (hper : ∀ x, dualV B (x + 1) = dualV B x)
    (hfun : ∀ x, dualE c * dualV B (x + α) + (dualE c)⁻¹ * dualV B (x - α)
        + ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * dualV B x = (E : ℂ) * dualV B x)
    (n : ℤ) :
    (lam : ℂ) * (cF (dualV B) (n + 1) + cF (dualV B) (n - 1))
      + ((2 * Real.cos (2 * Real.pi * ((n : ℝ) * α + c)) : ℝ) : ℂ) * cF (dualV B) n
      = (E : ℂ) * cF (dualV B) n := by
  set A : ℝ → ℂ := fun x => dualE c * dualV B (x + α) with hA
  set Bf : ℝ → ℂ := fun x => (dualE c)⁻¹ * dualV B (x - α) with hBf
  set C : ℝ → ℂ := fun x => ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * dualV B x with hC
  set D : ℝ → ℂ := fun x => (E : ℂ) * dualV B x with hD
  -- the two sides have equal `n`-th Fourier coefficient
  have hkey : cF (fun x => A x + Bf x + C x) n = cF D n := by
    simpa only [hA, hBf, hC, hD] using cF_congr hfun n
  -- continuity of the four pieces
  have hshiftA : Continuous (fun x : ℝ => dualV B (x + α)) :=
    hcont.comp (by fun_prop)
  have hshiftB : Continuous (fun x : ℝ => dualV B (x - α)) :=
    hcont.comp (by fun_prop)
  have contA : Continuous A := by rw [hA]; exact continuous_const.mul hshiftA
  have contB : Continuous Bf := by rw [hBf]; exact continuous_const.mul hshiftB
  have hcoefcont : Continuous (fun x : ℝ => ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (by fun_prop)
  have contC : Continuous C := by rw [hC]; exact hcoefcont.mul hcont
  have contD : Continuous D := by rw [hD]; exact continuous_const.mul hcont
  -- split `cF` over the sum
  have hsplit : cF (fun x => A x + Bf x + C x) n = (cF A n + cF Bf n) + cF C n := by
    rw [cF_add (f := fun x => A x + Bf x) (g := C) (contA.add contB) contC n,
        cF_add (f := A) (g := Bf) contA contB n]
  have keyAB : (cF A n + cF Bf n) + cF C n = (E : ℂ) * cF (dualV B) n := by
    rw [← hsplit, hkey]
    rw [show cF D n = (E : ℂ) * cF (dualV B) n from by rw [hD, cF_const_mul]]
  -- the three shifted / modulated terms
  have hcA : cF A n = dualE c * (chr n α * cF (dualV B) n) := by
    rw [hA, cF_const_mul, cF_shift (dualV B) hper α n]
  have hcB : cF Bf n = (dualE c)⁻¹ * (chr (-n) α * cF (dualV B) n) := by
    rw [hBf, cF_const_mul, cF_shift_sub (dualV B) hper α n]
  have hcC : cF C n = (lam : ℂ) * (cF (dualV B) (n - 1) + cF (dualV B) (n + 1)) := by
    rw [hC]
    have hfac : (fun x => ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * dualV B x)
        = (fun x => (lam : ℂ) * (((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * dualV B x)) := by
      funext x
      have hcoef : ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)
          = (lam : ℂ) * ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) := by push_cast; ring
      rw [hcoef]; ring
    rw [hfac, cF_const_mul, cF_two_cos_mul (dualV B) hcont n]
  -- combine the two shift terms into the single cosine factor
  have hcoeff : dualE c * (chr n α * cF (dualV B) n)
      + (dualE c)⁻¹ * (chr (-n) α * cF (dualV B) n)
      = ((2 * Real.cos (2 * Real.pi * ((n : ℝ) * α + c)) : ℝ) : ℂ) * cF (dualV B) n := by
    rw [← mul_assoc (dualE c) (chr n α) (cF (dualV B) n),
        ← mul_assoc (dualE c)⁻¹ (chr (-n) α) (cF (dualV B) n), ← add_mul]
    rw [show dualE c * chr n α + (dualE c)⁻¹ * chr (-n) α
        = ((2 * Real.cos (2 * Real.pi * ((n : ℝ) * α + c)) : ℝ) : ℂ) from by
      rw [show chr (-n) α = chr n (-α) from (chr_neg_arg n α).symm]
      exact dualE_chr_cos c n α]
  -- the assembled recurrence, with the two cos-terms in the "wrong" order
  have hbase : ((2 * Real.cos (2 * Real.pi * ((n : ℝ) * α + c)) : ℝ) : ℂ) * cF (dualV B) n
      + (lam : ℂ) * (cF (dualV B) (n - 1) + cF (dualV B) (n + 1))
      = (E : ℂ) * cF (dualV B) n := by
    have h1 : cF A n + cF Bf n
        = ((2 * Real.cos (2 * Real.pi * ((n : ℝ) * α + c)) : ℝ) : ℂ) * cF (dualV B) n := by
      rw [hcA, hcB]; exact hcoeff
    rw [← h1, ← hcC]
    exact keyAB
  rw [show cF (dualV B) (n + 1) + cF (dualV B) (n - 1)
      = cF (dualV B) (n - 1) + cF (dualV B) (n + 1) from add_comm _ _]
  exact (add_comm _ _).trans hbase

end Work.TMPuig
