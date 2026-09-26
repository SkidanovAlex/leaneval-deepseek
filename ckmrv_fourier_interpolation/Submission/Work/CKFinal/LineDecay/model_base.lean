import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs

/-!
# Shared definitions for the "model identity" of the line-decay computation

The model identity (CKMRV's `P₄ ≡ 0`) says that the horizontal-edge contributions of the cusp
model `𝒢_G` over the two rectangles `[0,1]×[H,H]` and `[-1,0]×[H,H]` cancel the closed-form
`highPart`.  Expanding `Gmodel` in the second variable reduces it to two scalar "one-variable"
integral identities, for which the following abbreviations are convenient.

* `Eexp k x = e^{ikx}` (`k`, `x` real);
* `QA k = ∫₀¹ e^{ikx}dx`, `QB k = ∫₋₁⁰ e^{ikx}dx`;
* `PA k = ∫₀¹ (x+i-1)e^{ikx}dx`, `PB k = ∫₋₁⁰ (x+i+1)e^{ikx}dx`;
* `A0 k = QA k - QB k`, `A1 k = PA k - PB k`.

The two scalar identities are
`i·A0 k = -k·psi1 k` and `i·A1 k = -i·psi1 k·(k+1)`.
-/

noncomputable section

open MeasureTheory UpperHalfPlane

namespace Work.CKFinal.LineDecay

/-- `e^{ikx}` for real `k` and `x`. -/
def Eexp (k x : ℝ) : ℂ := Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))

/-- `∫₀¹ e^{ikx}dx`. -/
def QA (k : ℝ) : ℂ := ∫ x in (0 : ℝ)..1, Eexp k x

/-- `∫₋₁⁰ e^{ikx}dx`. -/
def QB (k : ℝ) : ℂ := ∫ x in (-1 : ℝ)..0, Eexp k x

/-- `∫₀¹ (x+i-1)e^{ikx}dx`. -/
def PA (k : ℝ) : ℂ := ∫ x in (0 : ℝ)..1, ((x : ℂ) + Complex.I - 1) * Eexp k x

/-- `∫₋₁⁰ (x+i+1)e^{ikx}dx`. -/
def PB (k : ℝ) : ℂ := ∫ x in (-1 : ℝ)..0, ((x : ℂ) + Complex.I + 1) * Eexp k x

/-- `A0 k = ∫₀¹ e^{ikx}dx - ∫₋₁⁰ e^{ikx}dx`. -/
def A0 (k : ℝ) : ℂ := QA k - QB k

/-- `A1 k = ∫₀¹ (x+i-1)e^{ikx}dx - ∫₋₁⁰ (x+i+1)e^{ikx}dx`. -/
def A1 (k : ℝ) : ℂ := PA k - PB k

/-- The split point `H = 1`, as a complex number. -/
lemma hsplit_coe : ((Work.CKFinal.hsplit : ℝ) : ℂ) = 1 := by
  simp [Work.CKFinal.hsplit]

/-- `e^{-2πi(w+1)} = e^{-2πiw}`: the cusp model is invariant under `z ↦ z+1`. -/
lemma exp_per_add (w : ℂ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (w + 1)))
      = Complex.exp (-(2 * Real.pi * Complex.I * w)) := by
  rw [show -(2 * Real.pi * Complex.I * (w + 1))
      = -(2 * Real.pi * Complex.I * w) - (2 * Real.pi * Complex.I) by ring_nf,
    Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]

/-- `e^{-2πi(w-1)} = e^{-2πiw}`. -/
lemma exp_per_sub (w : ℂ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (w - 1)))
      = Complex.exp (-(2 * Real.pi * Complex.I * w)) := by
  rw [show -(2 * Real.pi * Complex.I * (w - 1))
      = -(2 * Real.pi * Complex.I * w) + (2 * Real.pi * Complex.I) by ring_nf,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- `e^{ik(x+i)} = e^{-k}e^{ikx}`: the exponential factor splits at height `H = 1`. -/
lemma exp_split (k x : ℝ) :
    Complex.exp (Complex.I * (k : ℂ) * ((x : ℂ) + Complex.I))
      = Complex.exp (-(k : ℂ)) * Eexp k x := by
  rw [show Complex.I * (k : ℂ) * ((x : ℂ) + Complex.I)
      = -(k : ℂ) + Complex.I * (k : ℂ) * (x : ℂ) by
        have h : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
        linear_combination (k : ℂ) * h, Complex.exp_add]
  rfl

/-- `e^{-2πiw}e^{ikw} = e^{i(k-2π)w}`. -/
lemma mul_exp (k : ℝ) (w : ℂ) :
    Complex.exp (-(2 * Real.pi * Complex.I * w)) * Complex.exp (Complex.I * (k : ℂ) * w)
      = Complex.exp (Complex.I * ((k : ℂ) - ((2 * Real.pi : ℝ) : ℂ)) * w) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end Work.CKFinal.LineDecay
