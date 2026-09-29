import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Avalanche.rift
import Submission.Work.Avalanche.svd

/-!
# Definitions for the weak avalanche estimate (`Work.TMC7Core.Scale.avalanche_weak`)

For `X, Y : Matrix (Fin 2) (Fin 2) ℂ` the *rift* is
`rift X Y = ‖XY‖_F / (‖X‖_F ‖Y‖_F) ∈ (0, 1]`, the ratio measuring how much of the maximal
possible growth the product `X * Y` achieves.

Writing `W = U_W · diag(a,a⁻¹) · V_Wᴴ`, `X = U_X · diag(b,b⁻¹) · V_Xᴴ`,
`M = U_M · diag(c,c⁻¹) · V_Mᴴ` (unitary `U_·, V_·`, `a,b,c ≥ 1`), and putting `T = V_Wᴴ U_X`,
`R = V_Xᴴ U_M`, `q = ‖T 0 0‖²`, `α = ‖R 0 0‖²`, one has exactly

* `rift W X ^ 2 = Phi a (pOf b q) (FOf b)`,
* `frob (diag(b,b⁻¹) * R * diag(c,c⁻¹))² = FZ b c α`,

and the one-step estimate compares `Phi a (first row norm² of D_b R D_c) (FZ b c α)` with
`Phi a (pOf b q) (FOf b)`.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

namespace Work.TMC7Core.Scale

/-- The rift `R(X,Y) = ‖XY‖_F / (‖X‖_F ‖Y‖_F)`. -/
def rift (X Y : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := frob (X * Y) / (frob X * frob Y)

/-- `FZ b c α = ‖diag(b,b⁻¹) * R * diag(c,c⁻¹)‖_F²` for a unitary `R` with `‖R 0 0‖² = α`. -/
def FZ (b c α : ℝ) : ℝ :=
  b ^ 2 * c ^ 2 * α + b ^ 2 * (c ^ 2)⁻¹ * (1 - α) + (b ^ 2)⁻¹ * c ^ 2 * (1 - α)
    + (b ^ 2)⁻¹ * (c ^ 2)⁻¹ * α

/-- `pOf b q = ‖first row of diag(b,b⁻¹) * T‖²` for a unitary `T` with `‖T 0 0‖² = q`. -/
def pOf (b q : ℝ) : ℝ := b ^ 2 * q + (b ^ 2)⁻¹ * (1 - q)

/-- `FOf b = ‖diag(b,b⁻¹)‖_F² = b² + b⁻²`. -/
def FOf (b : ℝ) : ℝ := b ^ 2 + (b ^ 2)⁻¹

/-- `Phi a p F = ‖diag(a,a⁻¹) * Z‖_F² / ((a²+a⁻²) ‖Z‖_F²)` where `p` is the squared norm of
the first row of `Z` and `F = ‖Z‖_F²`. -/
def Phi (a p F : ℝ) : ℝ := (a ^ 2 * p + (a ^ 2)⁻¹ * (F - p)) / ((a ^ 2 + (a ^ 2)⁻¹) * F)

end Work.TMC7Core.Scale
