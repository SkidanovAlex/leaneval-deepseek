import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.LocCantor.Defs

/-!
# C17 (`P_LocCantor`) — the Bloch wave of a decaying eigenfunction

(AJ §5, items (5.1)–(5.12).)  Given `u ≠ 0` with `amoAct α λ θ u = E u` and `ExpDecay u`,
its Fourier transform `U = fourier u` is analytic and the Bloch vector
`W(x) = (U(x)e^{2πiθ}, U(x-α))` satisfies `W(x+α) = e^{-2πiθ} S_{λ⁻¹,E/λ}(x) W(x)`, whence
the real matrix `A = [Re W, Im W]` satisfies `A(x+α) = S_{λ⁻¹,E/λ}(x) A(x) R_θ`, i.e.
`A⁻¹` conjugates the dual cocycle to the rotation `R_{-θ}`.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory Filter Topology Set

namespace Work.TMComp
open Work.TMContract

variable {α lam θ E : ℝ} {u : ℤ → ℂ}

/-- `e^{iy} + e^{-iy} = 2 cos y`. -/
theorem exp_add_exp_neg_cos (y : ℝ) :
    Complex.exp (y * Complex.I) + Complex.exp (-(y * Complex.I)) = ((2 * Real.cos y : ℝ) : ℂ) := by
  have h1 : Complex.exp (y * Complex.I) = ((Real.cos y : ℝ) : ℂ) + ((Real.sin y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h2 : Complex.exp (-(y * Complex.I)) = ((Real.cos y : ℝ) : ℂ) - ((Real.sin y : ℝ) : ℂ) * Complex.I := by
    rw [show -(y * Complex.I) = (-y) * Complex.I by ring, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [h1, h2]
  push_cast
  ring

/-- `e^{-z} e^{z} = 1`. -/
theorem exp_neg_mul_exp (z : ℂ) : Complex.exp (-z) * Complex.exp z = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- `e^{-z}(A(w e^{z})) = Aw`. -/
theorem exp_neg_mul_mul (z A w : ℂ) : Complex.exp (-z) * (A * (w * Complex.exp z)) = A * w := by
  rw [show Complex.exp (-z) * (A * (w * Complex.exp z))
      = (A * w) * (Complex.exp (-z) * Complex.exp z) by ring, exp_neg_mul_exp, mul_one]

/-- `e^{-z}(w e^{z}) = w`. -/
theorem exp_neg_mul_exp_mul (z w : ℂ) : Complex.exp (-z) * (w * Complex.exp z) = w := by
  rw [show Complex.exp (-z) * (w * Complex.exp z) = w * (Complex.exp (-z) * Complex.exp z) by ring,
    exp_neg_mul_exp, mul_one]

/-- Real and imaginary parts of `e^{-2πiθ}`. -/
theorem exp_neg_two_pi_re (θ : ℝ) :
    (Complex.exp (-(2 * Real.pi * θ * Complex.I))).re = Real.cos (2 * Real.pi * θ) := by
  rw [Complex.exp_re]
  simp [Real.cos_neg]

theorem exp_neg_two_pi_im (θ : ℝ) :
    (Complex.exp (-(2 * Real.pi * θ * Complex.I))).im = -Real.sin (2 * Real.pi * θ) := by
  rw [Complex.exp_im]
  simp [Real.sin_neg]

/-- The scalar identity obtained from the Fourier transform of the eigenvalue equation,
solved for `U(x+α)e^{2πiθ}` (before dividing by `λ`). -/
theorem bloch_scalar
    (hident : ∀ x : ℝ,
      (((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) * fourier u x
        + (lam : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u (x + α)
        + (lam : ℂ) * Complex.exp (-(2 * Real.pi * θ * Complex.I)) * fourier u (x - α)
      = (E : ℂ) * fourier u x) (x : ℝ) :
    (lam : ℂ) * (fourier u (x + α) * Complex.exp (2 * Real.pi * θ * Complex.I))
      = ((E : ℂ) - ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) * fourier u x
        - (lam : ℂ) * Complex.exp (-(2 * Real.pi * θ * Complex.I)) * fourier u (x - α) := by
  have h := hident x
  have h' : (E : ℂ) * fourier u x
      = ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) * fourier u x
        + (lam : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u (x + α)
        + (lam : ℂ) * Complex.exp (-(2 * Real.pi * θ * Complex.I)) * fourier u (x - α) := h.symm
  rw [sub_mul, h']
  ring

/-- First component of the Bloch relation (all coercions pushed). -/
theorem bloch_comp0
    (hident : ∀ x : ℝ,
      (((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) * fourier u x
        + (lam : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u (x + α)
        + (lam : ℂ) * Complex.exp (-(2 * Real.pi * θ * Complex.I)) * fourier u (x - α)
      = (E : ℂ) * fourier u x)
    (hlam : lam ≠ 0) (x : ℝ) :
    fourier u (x + α) * Complex.exp (2 * Real.pi * θ * Complex.I)
      = ((((E - 2 * Real.cos (2 * Real.pi * x)) * lam⁻¹ : ℝ) : ℂ)) * fourier u x
        - Complex.exp (-(2 * Real.pi * θ * Complex.I)) * fourier u (x - α) := by
  have hlamC : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  have hs := bloch_scalar hident x
  refine mul_left_cancel₀ (a := (lam : ℂ)) hlamC ?_
  rw [hs, sub_mul]
  push_cast
  field_simp

/-- The Bloch relation, componentwise: `W(x+α) = e^{-2πiθ} S(x) W(x)`, first component. -/
theorem bloch_component0
    (hident : ∀ x : ℝ,
      (((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) * fourier u x
        + (lam : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u (x + α)
        + (lam : ℂ) * Complex.exp (-(2 * Real.pi * θ * Complex.I)) * fourier u (x - α)
      = (E : ℂ) * fourier u x)
    (hlam : lam ≠ 0) (x : ℝ) :
    blochVec α θ u (x + α) 0
      = Complex.exp (-(2 * Real.pi * θ * Complex.I)) *
          ((((E - 2 * Real.cos (2 * Real.pi * x)) * lam⁻¹ : ℝ) : ℂ) * blochVec α θ u x 0
            - blochVec α θ u x 1) := by
  have h0 := bloch_comp0 hident hlam x
  simp only [blochVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.isValue]
  rw [h0, mul_sub]
  congr 1
  exact (exp_neg_mul_mul _ _ _).symm

/-- The Bloch relation, componentwise: second component (trivial). -/
theorem bloch_component1 (x : ℝ) :
    blochVec α θ u (x + α) 1
      = Complex.exp (-(2 * Real.pi * θ * Complex.I)) * blochVec α θ u x 0 := by
  simp only [blochVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.isValue]
  rw [add_sub_cancel_right]
  exact (exp_neg_mul_exp_mul _ _).symm

/-- The real conjugacy relation: `A(x+α) = S_{λ⁻¹,E/λ}(x) · A(x) · R_θ`, where
`A = [Re W, Im W]`. -/
theorem blochReal_rel
    (hident : ∀ x : ℝ,
      (((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) * fourier u x
        + (lam : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u (x + α)
        + (lam : ℂ) * Complex.exp (-(2 * Real.pi * θ * Complex.I)) * fourier u (x - α)
      = (E : ℂ) * fourier u x)
    (hlam : lam ≠ 0) (x : ℝ) :
    blochReal α θ u (x + α) = tmR lam⁻¹ (E * lam⁻¹) x * blochReal α θ u x * rot θ := by
  have h0 := bloch_component0 hident hlam x
  have h1 := bloch_component1 (α := α) (θ := θ) (u := u) x
  have hA : (((E - 2 * Real.cos (2 * Real.pi * x)) * lam⁻¹ : ℝ) : ℂ)
      = ((E : ℂ) - ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) * (lam : ℂ)⁻¹ := by
    push_cast
    ring
  have hr0 : (blochVec α θ u (x + α) 0).re
      = Real.cos (2 * Real.pi * θ)
          * (((E - 2 * Real.cos (2 * Real.pi * x)) * lam⁻¹) * (blochVec α θ u x 0).re
              - (blochVec α θ u x 1).re)
        + Real.sin (2 * Real.pi * θ)
          * (((E - 2 * Real.cos (2 * Real.pi * x)) * lam⁻¹) * (blochVec α θ u x 0).im
              - (blochVec α θ u x 1).im) := by
    rw [congrArg Complex.re h0]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, exp_neg_two_pi_re,
      exp_neg_two_pi_im]
    ring
  have hi0 : (blochVec α θ u (x + α) 0).im
      = Real.cos (2 * Real.pi * θ)
          * (((E - 2 * Real.cos (2 * Real.pi * x)) * lam⁻¹) * (blochVec α θ u x 0).im
              - (blochVec α θ u x 1).im)
        - Real.sin (2 * Real.pi * θ)
          * (((E - 2 * Real.cos (2 * Real.pi * x)) * lam⁻¹) * (blochVec α θ u x 0).re
              - (blochVec α θ u x 1).re) := by
    rw [congrArg Complex.im h0]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, exp_neg_two_pi_re,
      exp_neg_two_pi_im]
    ring
  have hr1 : (blochVec α θ u (x + α) 1).re
      = Real.cos (2 * Real.pi * θ) * (blochVec α θ u x 0).re
        + Real.sin (2 * Real.pi * θ) * (blochVec α θ u x 0).im := by
    rw [congrArg Complex.re h1]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, exp_neg_two_pi_re,
      exp_neg_two_pi_im]
    ring
  have hi1 : (blochVec α θ u (x + α) 1).im
      = Real.cos (2 * Real.pi * θ) * (blochVec α θ u x 0).im
        - Real.sin (2 * Real.pi * θ) * (blochVec α θ u x 0).re := by
    rw [congrArg Complex.im h1]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, exp_neg_two_pi_re,
      exp_neg_two_pi_im]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [blochReal, Matrix.mul_fin_two, tmR, rot]
      simp [hr0, hi0, hr1, hi1]
      ring

end Work.TMComp
