/-
# The `(p₁,p₂)`-coefficient of the §6 model kernel: the double integral over `[0,1]²`

The kernel `K` of the §6 model operator is recovered from its symbol `σ` by the Fourier
coefficient formula

  `K(p₁,p₂) = ∫₀¹ ∫₀¹ σ(x,y) e(-p₁x - p₂y) dx dy`,   `e(z) = exp(2πiz)`

(`Work.KMTPlan.A6.coeff2`).  Here `σ` is a *finite* sum of pure exponential monomials

  `K(a₁,a₂) e(a₁x + a₂y) · (κ(a₃) e(a₃x)) · (κ'(a₄) e(a₄y))`,

the `(a₁,a₂)`-term of the kernel-side sum and the `a₃`,`a₄` terms of the one-dimensional
symbols `symSeq κ`, `symSeq κ'`.  This module computes its double Fourier coefficient:
**the exponentials collapse to the orthogonality relation** `∫₀¹ e(n x) dx = δ_{n,0}`
(`Work.KMTPlan.A6.integral_eeC_int`), so the coefficient vanishes unless the frequencies
match,

  `a₁ + a₃ = p₁`, `a₂ + a₄ = p₂`,

in which case it is `K(a₁,a₂) κ(a₃) κ'(a₄)`.  This is the "product of two one-dimensional
characters" bookkeeping step of the §6 model approximation `mod-approx`.

The only analytic input is the orthogonality of the characters; the rest is the
factorisation of `e(Σ)` into one-dimensional characters (`eeC_add`), the two interval
integrals then decouple and are evaluated by `integral_eeC_int`.  The helper
`eeC_mul_four` collects four one-variable exponential factors into a single one.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymSeq_coeff1

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral
open scoped BigOperators ENNReal

noncomputable section

/-- Four exponential factors of the shape occurring in the §6 model kernel combine into a
single character: `e(A) e(c x) e(d y) e(B) = e(A + c x + d y + B)`. -/
lemma eeC_mul_four (A c d B x y : ℝ) :
    eeC A * eeC (c * x) * eeC (d * y) * eeC B = eeC (A + c * x + d * y + B) := by
  rw [← eeC_add A (c * x), ← eeC_add (A + c * x) (d * y), ← eeC_add (A + c * x + d * y) B]

/-- The `(p₁,p₂)`-th Fourier coefficient of the product of a kernel symbol with two
one-dimensional symbols is the product of the coefficients along the matching frequencies:
integrating the exponential factors over `[0,1]²` gives `δ`-functions. -/
theorem integral_integral_kernelTerm (K : ℤ → ℤ → ℂ) (κ κ' : ℤ → ℂ) (p₁ p₂ : ℤ)
    (w : (ℤ × ℤ) × (ℤ × ℤ)) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        ((K w.1.1 w.1.2 * Work.KMTPlan.A6.eeC (w.1.1 * x + w.1.2 * y))
          * (κ w.2.1 * Work.KMTPlan.A6.eeC (w.2.1 * x)
              * (κ' w.2.2 * Work.KMTPlan.A6.eeC (w.2.2 * y))))
          * Work.KMTPlan.A6.eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)
      = K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2
          * (if w.1.1 + w.2.1 = p₁ then 1 else 0)
          * (if w.1.2 + w.2.2 = p₂ then 1 else 0) := by
  -- Step 1: the integrand is a constant times a one-variable character in `x` times one in `y`.
  have hpt : ∀ x y : ℝ,
      ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y))
        * (κ w.2.1 * eeC (w.2.1 * x)
            * (κ' w.2.2 * eeC (w.2.2 * y))))
        * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)
      = (K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
          * (eeC (((w.1.1 + w.2.1 - p₁ : ℤ) : ℝ) * x)
              * eeC (((w.1.2 + w.2.2 - p₂ : ℤ) : ℝ) * y)) := by
    intro x y
    rw [show ((K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y))
        * (κ w.2.1 * eeC (w.2.1 * x)
            * (κ' w.2.2 * eeC (w.2.2 * y))))
        * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)
      = (K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
        * (eeC (w.1.1 * x + w.1.2 * y) * eeC ((w.2.1 : ℝ) * x)
            * eeC ((w.2.2 : ℝ) * y) * eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)) from by ring]
    rw [eeC_mul_four, ← eeC_add]
    congr 1
    congr 1
    push_cast
    ring
  simp only [hpt]
  -- Step 2: the inner integral in `y`: the `y`-character is orthogonal.
  have hinner : ∀ x : ℝ,
      (∫ y in (0:ℝ)..1, (K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
          * (eeC (((w.1.1 + w.2.1 - p₁ : ℤ) : ℝ) * x)
              * eeC (((w.1.2 + w.2.2 - p₂ : ℤ) : ℝ) * y)))
      = (K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2) * eeC (((w.1.1 + w.2.1 - p₁ : ℤ) : ℝ) * x)
          * (if (w.1.2 + w.2.2 - p₂ : ℤ) = 0 then 1 else 0) := by
    intro x
    rw [show (fun y : ℝ => (K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
          * (eeC (((w.1.1 + w.2.1 - p₁ : ℤ) : ℝ) * x)
              * eeC (((w.1.2 + w.2.2 - p₂ : ℤ) : ℝ) * y)))
        = (fun y : ℝ => ((K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
            * eeC (((w.1.1 + w.2.1 - p₁ : ℤ) : ℝ) * x))
            * eeC (((w.1.2 + w.2.2 - p₂ : ℤ) : ℝ) * y)) from by funext y; ring]
    rw [intervalIntegral.integral_const_mul, integral_eeC_int]
  -- Step 3: the outer integral in `x`.
  have houter : (∫ x in (0:ℝ)..1, (K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
          * eeC (((w.1.1 + w.2.1 - p₁ : ℤ) : ℝ) * x)
          * (if (w.1.2 + w.2.2 - p₂ : ℤ) = 0 then 1 else 0))
      = (K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
          * (if (w.1.2 + w.2.2 - p₂ : ℤ) = 0 then 1 else 0)
          * (if (w.1.1 + w.2.1 - p₁ : ℤ) = 0 then 1 else 0) := by
    rw [show (fun x : ℝ => (K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
          * eeC (((w.1.1 + w.2.1 - p₁ : ℤ) : ℝ) * x)
          * (if (w.1.2 + w.2.2 - p₂ : ℤ) = 0 then 1 else 0))
        = (fun x : ℝ => ((K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
            * (if (w.1.2 + w.2.2 - p₂ : ℤ) = 0 then 1 else 0))
            * eeC (((w.1.1 + w.2.1 - p₁ : ℤ) : ℝ) * x)) from by funext x; ring]
    rw [intervalIntegral.integral_const_mul, integral_eeC_int]
  -- Step 4: assemble.
  rw [show (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
          * (eeC (((w.1.1 + w.2.1 - p₁ : ℤ) : ℝ) * x)
              * eeC (((w.1.2 + w.2.2 - p₂ : ℤ) : ℝ) * y)))
      = ∫ x in (0:ℝ)..1, ((K w.1.1 w.1.2 * κ w.2.1 * κ' w.2.2)
          * eeC (((w.1.1 + w.2.1 - p₁ : ℤ) : ℝ) * x)
          * (if (w.1.2 + w.2.2 - p₂ : ℤ) = 0 then 1 else 0)) from by
      apply intervalIntegral.integral_congr
      intro x _
      exact hinner x]
  rw [houter]
  rw [show ((if (w.1.1 + w.2.1 - p₁ : ℤ) = 0 then (1:ℂ) else 0))
      = (if w.1.1 + w.2.1 = p₁ then 1 else 0) from by simp only [sub_eq_zero]]
  rw [show ((if (w.1.2 + w.2.2 - p₂ : ℤ) = 0 then (1:ℂ) else 0))
      = (if w.1.2 + w.2.2 = p₂ then 1 else 0) from by simp only [sub_eq_zero]]
  ring

end

end Work.KMTPlan.A6
