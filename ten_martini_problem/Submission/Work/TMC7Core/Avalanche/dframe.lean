import Mathlib
import Submission.Work.TMC7Core.Defs

/-!
# The `SVD` normal form of a chain of `SL₂(ℂ)` matrices

Write each `A j = U j · diag(σ j, σ j⁻¹) · V jᴴ` (possible with unitaries `U j`, `V j` and
`σ j ≥ 1` by `svd_ge_one`), put `W j = V (j+1)ᴴ · U j`, and
`N k = D k · W (k-1) · D (k-1) ⋯ W 0 · D 0`.  Then `frob (matProd A n) = frob (N (n-1))` and
`frob (A (j+1) * A j) = frob (D (j+1) * W j * D j)`, so the avalanche principle reduces to
statements about the abstract chain `(D k, W k)` of diagonal scalings and unitaries.

This file only contains the definitions (no proofs), so that every other module can import it.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

namespace Work.TMC7Core.Avalanche

/-- `diag(s, s⁻¹)` as a complex `2×2` matrix. -/
def Dm (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal ![((s : ℝ) : ℂ), ((s⁻¹ : ℝ) : ℂ)]

/-- `N k = D k · W (k-1) · D (k-1) ⋯ W 0 · D 0` (so `N 0 = D 0`). -/
def Nmat (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => Dm (s 0)
  | (k + 1) => Dm (s (k + 1)) * W k * Nmat s W k

/-- `G k = N k · (N k)ᴴ`, the (left) Gram matrix of the truncated product. -/
def Gmat (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Nmat s W k * (Nmat s W k)ᴴ

lemma Nmat_succ (s : ℕ → ℝ) (W : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    Nmat s W (k + 1) = Dm (s (k + 1)) * W k * Nmat s W k := rfl

end Work.TMC7Core.Avalanche
