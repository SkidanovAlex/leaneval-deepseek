/-
# Duality definitions for Puig's argument (`TMPuig`)

These are the definitions used by `Work.TMPuig.dual_l2_solution` and the lemmas
delegated for it.  The point of the file is that the *statements* of those lemmas
can be written in this vocabulary (so colleagues can prove them independently of
the main file).

Context: `B : ℝ → SL(2,ℝ)` is `1`-periodic and conjugates the transfer cocycle to
the constant rotation: `B (x + α) * tmR λ E x = rot c * B x`.  Writing
`w = (1,-i) ∈ ℂ²` (an eigenvector of `rot c` with eigenvalue `e^{2πic}`), the
periodic function `x ↦ B x⁻¹ *ᵥ w` has first component
`V x = B x 1 1 + i * B x 0 1`.  It satisfies the dual ("Bloch") equation
`e^{2πic} V (x+α) + e^{-2πic} V (x-α) + 2λ cos(2πx) V x = E V x`, and its Fourier
coefficients are the `ℓ²` solution of the dual almost Mathieu equation.
-/
import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMPuig.Defs

open Matrix

noncomputable section

namespace Work.TMPuig

/-- Entrywise complexification of a real `2 × 2` matrix. -/
def dualC (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  M.map (fun r => (r : ℂ))

/-- `e^{2πic}`, the eigenvalue of `rot c` on the eigenvector `dualW`. -/
def dualE (c : ℝ) : ℂ := Complex.exp (((2 * Real.pi * c : ℝ)) * Complex.I)

/-- The eigenvector `(1,-i)` of `rot c` (with eigenvalue `e^{2πic}`). -/
def dualW : Fin 2 → ℂ := ![(1 : ℂ), -Complex.I]

/-- `V x = B x 1 1 + i * B x 0 1`: the first component of `B x⁻¹ *ᵥ dualW` (the
second component is `dualU B x 1 = -B x 1 0 - i * B x 0 0`).  This is the periodic
Bloch function whose Fourier coefficients solve the dual equation. -/
def dualV (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : ℂ :=
  ↑(B x 1 1) + Complex.I * ↑(B x 0 1)

/-- `dualU B x = B x⁻¹ *ᵥ dualW`, written out using `det B x = 1` (see
`dualC_mulVec_dualU`); its first component is `dualV B x`. -/
def dualU (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : Fin 2 → ℂ
  | 0 => dualV B x
  | 1 => -↑(B x 1 0) - Complex.I * ↑(B x 0 0)

theorem dualE_ne_zero (c : ℝ) : dualE c ≠ 0 := Complex.exp_ne_zero _

theorem dualU_zero (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : dualU B x 0 = dualV B x := rfl

theorem dualU_one (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) :
    dualU B x 1 = -↑(B x 1 0) - Complex.I * ↑(B x 0 0) := rfl

end Work.TMPuig
