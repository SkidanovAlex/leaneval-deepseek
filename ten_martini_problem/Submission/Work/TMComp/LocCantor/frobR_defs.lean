import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Scale.frob_map_ofReal_sq

/-!
# The real Frobenius norm of a `2 × 2` matrix

`frobR B` is the Frobenius norm of a real `2 × 2` matrix, i.e. the square root of the sum
of the squares of its four entries.  It is the real counterpart of
`Work.TMC7Core.frob` on the complexification:  `frobR B = frob (B.map Complex.ofRealHom)`.
-/

namespace Work.TMComp.LocCantor

/-- Frobenius norm of a real `2 × 2` matrix. -/
noncomputable def frobR (B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.sqrt (B 0 0 ^ 2 + B 0 1 ^ 2 + B 1 0 ^ 2 + B 1 1 ^ 2)

theorem frobR_nonneg (B : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ frobR B := Real.sqrt_nonneg _

theorem frobR_sq (B : Matrix (Fin 2) (Fin 2) ℝ) :
    frobR B ^ 2 = B 0 0 ^ 2 + B 0 1 ^ 2 + B 1 0 ^ 2 + B 1 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The real Frobenius norm is the complex one applied to the complexification. -/
theorem frob_map_eq_frobR (B : Matrix (Fin 2) (Fin 2) ℝ) :
    Work.TMC7Core.frob (B.map Complex.ofRealHom) = frobR B := by
  rw [Work.TMC7Core.frob, frobR]
  congr 1
  have h : ∀ x : ℝ, ‖Complex.ofRealHom x‖ ^ 2 = x ^ 2 := by
    intro x
    have h1 : (Complex.ofRealHom x : ℂ) = (x : ℂ) := rfl
    rw [h1, Complex.sq_norm, Complex.normSq_ofReal]
    ring
  simp only [Matrix.map_apply, h]

end Work.TMComp.LocCantor
