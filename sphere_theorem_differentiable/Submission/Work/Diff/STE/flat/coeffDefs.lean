import Mathlib
import Submission.Work.Diff.STE.flat.torus_uniqueness

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The symmetrised inverse-metric coefficients of the flat DeTurck principal part

This small module fixes the vocabulary used by `Work.Diff.STE.flat.coeffProps`.

For a real matrix `B` we write `symmInv B` for the *symmetrisation of its inverse*,
`symmInv B c d = (B⁻¹ c d + B⁻¹ d c)/2`.  It is the coefficient matrix of the principal part of
the linearised flat DeTurck operator: it must be *symmetric* for Gårding's estimate
(`Work.Diff.STE.flat.garding_param`) to apply, while the quadratic form of `symmInv B` is the same
as that of `B⁻¹` (the antisymmetric part contributes nothing to a quadratic form).

For a torus-valued function `u` we write `coeffA u t x := symmInv (reMat (u t x))`.
-/

noncomputable section

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped Matrix BigOperators

variable {n : ℕ}

/-- The symmetrisation of the inverse of a real matrix. -/
def symmInv (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun c d => (B⁻¹ c d + B⁻¹ d c) / 2

lemma symmInv_apply (B : Matrix (Fin n) (Fin n) ℝ) (c d : Fin n) :
    symmInv B c d = (B⁻¹ c d + B⁻¹ d c) / 2 := rfl

/-- `symmInv` is symmetric. -/
lemma symmInv_symm (B : Matrix (Fin n) (Fin n) ℝ) (c d : Fin n) :
    symmInv B c d = symmInv B d c := by
  simp only [symmInv]
  ring

/-- Swapping the two summation indices of a double sum. -/
lemma sum_sum_transpose (f : Fin n → Fin n → ℝ) :
    (∑ c, ∑ d, f d c) = ∑ c, ∑ d, f c d := by
  rw [Finset.sum_comm]

/-- The quadratic form of the symmetrised inverse equals the quadratic form of the inverse; the
antisymmetric part contributes nothing. -/
lemma symmInv_quadForm_eq (B : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    ∑ c, ∑ d, symmInv B c d * ξ c * ξ d = ∑ c, ∑ d, B⁻¹ c d * ξ c * ξ d := by
  have key : ∀ c d, symmInv B c d * ξ c * ξ d
      = 1/2 * (B⁻¹ c d * ξ c * ξ d) + 1/2 * (B⁻¹ d c * ξ c * ξ d) := by
    intro c d
    simp only [symmInv]
    ring
  have hcomm : ∀ c d, B⁻¹ c d * ξ d * ξ c = B⁻¹ c d * ξ c * ξ d := fun c d => by ring
  have h2 : (∑ c, ∑ d, B⁻¹ d c * ξ c * ξ d) = ∑ c, ∑ d, B⁻¹ c d * ξ c * ξ d := by
    rw [← sum_sum_transpose (fun c d => B⁻¹ d c * ξ c * ξ d)]
    simp only [hcomm]
  have hsum : (∑ c, ∑ d, (1/2 * (B⁻¹ c d * ξ c * ξ d) + 1/2 * (B⁻¹ d c * ξ c * ξ d)))
      = (1/2) * (∑ c, ∑ d, B⁻¹ c d * ξ c * ξ d)
        + (1/2) * (∑ c, ∑ d, B⁻¹ d c * ξ c * ξ d) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => key c d)), hsum, h2]
  ring

/-- The coefficient matrix of the principal part of the linearised flat DeTurck operator. -/
def coeffA (u : ℝ → Torus n) : ℝ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
  fun t x => symmInv (reMat (u t x))

lemma coeffA_apply (u : ℝ → Torus n) (t : ℝ) (x : Fin n → ℝ) (c d : Fin n) :
    coeffA u t x c d
      = (((reMat (u t x))⁻¹) c d + ((reMat (u t x))⁻¹) d c) / 2 := rfl

@[simp] lemma coeffA_symm (u : ℝ → Torus n) (t : ℝ) (x : Fin n → ℝ) (c d : Fin n) :
    coeffA u t x c d = coeffA u t x d c :=
  symmInv_symm (reMat (u t x)) c d

lemma coeffA_quadForm_eq (u : ℝ → Torus n) (t : ℝ) (x : Fin n → ℝ) (ξ : Fin n → ℝ) :
    ∑ c, ∑ d, coeffA u t x c d * ξ c * ξ d
      = ∑ c, ∑ d, ((reMat (u t x))⁻¹) c d * ξ c * ξ d :=
  symmInv_quadForm_eq (reMat (u t x)) ξ

lemma coeffA_unfold (u : ℝ → Torus n) (t : ℝ) (x : Fin n → ℝ) :
    coeffA u t x = symmInv (reMat (u t x)) := rfl

end Work.Diff.STE.flat
