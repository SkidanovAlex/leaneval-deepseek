import Submission.Work.TMC14Core.Weyl

/-!
# TMC14Core: the elementary matrix decomposition of the Bloch matrix

`blochMat` (defined in `TMC14Core.Rat`) is given entrywise as a sum of five
elementary contributions: the diagonal `2λ cos 2π(θ + i p/q)`, the superdiagonal
`E_{i,i+1}`, the subdiagonal `E_{i+1,i}` and the two corner entries
`e^{±2πik}` of the Bloch boundary condition.

This file names those five contributions (`bDiag`, `bSup`, `bSub`, `bTL`, `bBR`)
and proves `blochMat = bDiag + bSup + bSub + bTL + bBR`.
-/

open Matrix

noncomputable section

namespace Work.TMC14Core

/-- The diagonal part `2λ cos 2π(θ + i p/q)` of the Bloch matrix. -/
def bDiag (p : ℤ) (q : ℕ) (lam θ : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j =>
    (if i = j then ((2 * lam * Real.cos (2 * Real.pi * (θ + (i : ℝ) * (p : ℝ) / (q : ℝ))) : ℝ) : ℂ)
      else 0)

/-- The superdiagonal `E_{i,i+1}`. -/
def bSup (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j => (if (i : ℕ) + 1 = (j : ℕ) then (1 : ℂ) else 0)

/-- The subdiagonal `E_{i+1,i}`. -/
def bSub (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j => (if (j : ℕ) + 1 = (i : ℕ) then (1 : ℂ) else 0)

/-- The top-right corner `e^{2πik} E_{q-1,0}`. -/
def bTL (q : ℕ) (k : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j =>
    (if (i : ℕ) = q - 1 ∧ (j : ℕ) = 0 then
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) else 0)

/-- The bottom-left corner `e^{-2πik} E_{0,q-1}`. -/
def bBR (q : ℕ) (k : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  fun i j =>
    (if (i : ℕ) = 0 ∧ (j : ℕ) = q - 1 then
      Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ))) else 0)

/-- `star (e^{2πik}) = e^{-2πik}`. -/
theorem star_wShiftBeta (k : ℝ) :
    star (wShiftBeta k) = Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ))) := by
  rw [wShiftBeta, wPh_conj, wPh]
  congr 1
  push_cast
  ring

/-- The Bloch matrix is the sum of the five elementary matrices. -/
theorem blochMat_decomp (p : ℤ) (q : ℕ) (lam θ k : ℝ) :
    blochMat p q lam θ k = bDiag p q lam θ + bSup q + bSub q + bTL q k + bBR q k := by
  ext i j
  simp only [blochMat, bDiag, bSup, bSub, bTL, bBR, Matrix.add_apply]

end Work.TMC14Core
