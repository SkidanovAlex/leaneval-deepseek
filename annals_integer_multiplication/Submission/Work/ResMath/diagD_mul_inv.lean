import Mathlib
import Submission.Work.ResMath.defs

/-!
# `D = diag(e^{π α² β_ℓ²})` is invertible

`D` (paper §4.1, `HvdH.diagD`) is a diagonal matrix whose diagonal entries are the complex
numbers `e^{π α² β_ℓ²}` with `β_ℓ = tℓ/s - [tℓ/s] ∈ ℝ`.  Since the real exponential is strictly
positive, every diagonal entry is a nonzero complex number, so `D` is invertible with explicit
inverse `diag(1/D_{ℓℓ})`.  Lean's `Matrix` (finite index type `Fin s`) is a ring, so this witness
is simultaneously a left and a right inverse.
-/

namespace Work.ResMath

theorem diagD_mul_inv (s t α : ℕ) :
    ∃ Dinv : Matrix (Fin s) (Fin s) ℂ, HvdH.diagD s t α * Dinv = 1 ∧ Dinv * HvdH.diagD s t α = 1 := by
  -- `D` is literally `diagonal d` with `d ℓ = ↑(exp (π α² β_ℓ²))`.
  set d : Fin s → ℂ :=
    fun ℓ => ((Real.exp (Real.pi * (α : ℝ) ^ 2 * HvdH.betaR s t ℓ ^ 2) : ℝ) : ℂ) with hd
  have hdiag : HvdH.diagD s t α = Matrix.diagonal d := rfl
  -- every diagonal entry is nonzero (a positive real, seen in `ℂ`)
  have hne : ∀ ℓ, d ℓ ≠ 0 := fun ℓ => Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
  refine ⟨Matrix.diagonal (fun ℓ => (d ℓ)⁻¹), ?_, ?_⟩
  · rw [hdiag, Matrix.diagonal_mul_diagonal]
    simp [hne, Matrix.diagonal_one]
  · rw [hdiag, Matrix.diagonal_mul_diagonal]
    simp [hne, Matrix.diagonal_one]

end Work.ResMath
