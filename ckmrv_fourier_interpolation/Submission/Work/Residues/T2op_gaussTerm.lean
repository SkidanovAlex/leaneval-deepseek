/-
# The `(T-I)²`-defect of the Gaussian `e^{πiτr²}`

CKMRV Proposition 5.1 computes the two defects of the kernel transform `F₂`; the *Gaussian*
summand `F₁ = e^{πiτr²}` of (5.2) has the defect

  `F₁|^τ_{d/2}(T-I)² = -4 e^{πir²(τ+1)} sin²(πr²/2)`

(a weight-independent computation, since `j(T,τ) = 1`).  This file records that identity in
the form used by `Work.Residues.h5a_false`: with `q = e^{πir²}`,

  `T2op (gaussTerm · r) τ = (q-1)² e^{πiτr²} = -4 e^{πir²(τ+1)} sin²(πr²/2)`.

The single trigonometric input is `exp_I_sub_one_sq` below.
-/
import Mathlib
import Submission.Work.Kernels.Theorem31
import Submission.Work.Kernels.PhiAnnihilation

noncomputable section

open UpperHalfPlane

namespace Work.Residues

open Work.Kernels

/-- The elementary exponential identity `(e^{iz} - 1)² = -4 e^{iz} sin²(z/2)`, valid for every
complex `z`. -/
lemma exp_I_sub_one_sq (z : ℂ) :
    (Complex.exp (z * Complex.I) - 1) ^ 2
      = -4 * Complex.exp (z * Complex.I) * Complex.sin (z / 2) ^ 2 := by
  set v : ℂ := Complex.exp (z * Complex.I / 2) with hv
  have hvne : v ≠ 0 := by rw [hv]; exact Complex.exp_ne_zero _
  have hv2 : v ^ 2 = Complex.exp (z * Complex.I) := by
    rw [hv, sq, ← Complex.exp_add]
    congr 1
    ring
  have hsin : Complex.sin (z / 2) = (v⁻¹ - v) * Complex.I / 2 := by
    have h := Complex.two_sin (z / 2)
    have hneg : Complex.exp (-(z * Complex.I / 2)) = v⁻¹ := by
      rw [hv, Complex.exp_neg]
    rw [show (-(z / 2)) * Complex.I = -(z * Complex.I / 2) by ring] at h
    rw [show (z / 2) * Complex.I = z * Complex.I / 2 by ring] at h
    rw [hneg, hv] at h
    linear_combination h / 2
  have hsin' : ((v⁻¹ - v) * Complex.I / 2) ^ 2 = (v⁻¹ - v) ^ 2 * (-1) / 4 := by
    rw [div_pow, mul_pow, Complex.I_sq]
    ring
  have hv' : v * (v⁻¹ - v) = 1 - v ^ 2 := by
    rw [mul_sub, mul_inv_cancel₀ hvne, pow_two]
  have hsq : v ^ 2 * (v⁻¹ - v) ^ 2 = (v * (v⁻¹ - v)) ^ 2 := by ring
  rw [hsin, ← hv2, hsin']
  rw [show -4 * v ^ 2 * ((v⁻¹ - v) ^ 2 * (-1) / 4) = v ^ 2 * (v⁻¹ - v) ^ 2 by ring]
  rw [hsq, hv']
  ring

/-- **The `(T-I)²`-defect of the Gaussian.**  With `T2op F = F(·+2) - 2F(·+1) + F`, the Gaussian
`gaussTerm · r = e^{πiτr²}` satisfies
`T2op (gaussTerm · r) τ = -4 e^{πir²(τ+1)} sin²(πr²/2)`. -/
theorem T2op_gaussTerm (τ : UpperHalfPlane) (r : ℝ) :
    T2op (fun σ : UpperHalfPlane => gaussTerm σ r) τ
      = -4 * gaussTerm ((1 : ℝ) +ᵥ τ) r
        * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 := by
  have hcoef2 : (((2 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) = 2 + (τ : ℂ) := coe_vadd_two τ
  have hcoef1 : (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) = 1 + (τ : ℂ) := coe_vadd_one τ
  have h1 : gaussTerm ((1 : ℝ) +ᵥ τ) r
      = gaussTerm τ r * Complex.exp (Real.pi * (r : ℂ) ^ 2 * Complex.I) := by
    simp only [gaussTerm]
    rw [hcoef1]
    rw [show Real.pi * Complex.I * (1 + (τ : ℂ)) * (r : ℂ) ^ 2
        = Real.pi * Complex.I * (τ : ℂ) * (r : ℂ) ^ 2
          + Real.pi * (r : ℂ) ^ 2 * Complex.I by ring]
    rw [Complex.exp_add]
  have h2 : gaussTerm ((2 : ℝ) +ᵥ τ) r
      = gaussTerm τ r * Complex.exp (Real.pi * (r : ℂ) ^ 2 * Complex.I) ^ 2 := by
    simp only [gaussTerm]
    rw [hcoef2]
    rw [show Real.pi * Complex.I * (2 + (τ : ℂ)) * (r : ℂ) ^ 2
        = Real.pi * Complex.I * (τ : ℂ) * (r : ℂ) ^ 2
          + (Real.pi * (r : ℂ) ^ 2 * Complex.I + Real.pi * (r : ℂ) ^ 2 * Complex.I) by ring]
    rw [Complex.exp_add, Complex.exp_add]
    ring
  rw [T2op, h2, h1]
  rw [show gaussTerm τ r * Complex.exp (Real.pi * (r : ℂ) ^ 2 * Complex.I) ^ 2
        - 2 * (gaussTerm τ r * Complex.exp (Real.pi * (r : ℂ) ^ 2 * Complex.I)) + gaussTerm τ r
      = gaussTerm τ r
        * (Complex.exp (Real.pi * (r : ℂ) ^ 2 * Complex.I) - 1) ^ 2 by ring]
  rw [exp_I_sub_one_sq]
  ring

end Work.Residues
