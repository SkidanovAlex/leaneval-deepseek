import Mathlib.Analysis.Matrix.Order
import Submission.Work.BoseB4.GramQuadForm
import Submission.Work.BoseB4.PosSemidefOfQuadform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Every symmetric positive semidefinite kernel on a finite mode set is a Gram kernel

`Work.BoseB4.gram f g = ∑ l, f l * g l` is the Gram product on the coordinate space
`Fin m → ℝ` (see `Work.BoseB4.ModeFock`).  This module proves that a kernel
`K : Mode → Mode → ℝ` on a finite mode set is representable as the Gram kernel of a
family `f : Mode → Fin m → ℝ` **if and only if** it is symmetric and its quadratic
form is nonnegative.

The easy direction uses `gram_comm` and the positive semidefiniteness of a Gram
kernel (`Work.BoseB4.GramQuadForm`).  The converse builds the matrix `Matrix.of K`,
recognises it as positive semidefinite (`Work.BoseB4.PosSemidefOfQuadform`), factors
it as `B * Bᴴ` through the functional calculus of the C⋆-algebra of real matrices
(`CStarAlgebra.nonneg_iff_eq_mul_star_self`), and reads off the coordinate vectors
`l ↦ B i l` from the rows of `B` (reindexing `Mode ≃ Fin (card Mode)`).
-/

open scoped BigOperators
open scoped MatrixOrder
open Matrix

namespace Work.BoseB4

/-- A kernel `K : Mode → Mode → ℝ` on a finite mode set is the Gram kernel of a family
of coordinate vectors `f : Mode → Fin m → ℝ` if and only if `K` is symmetric and
positive semidefinite. -/
theorem Exists_gram_iff {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (K : Mode → Mode → ℝ) :
    (∃ (m : ℕ) (f : Mode → Fin m → ℝ), ∀ i j, Work.BoseB4.gram (f i) (f j) = K i j)
      ↔ ((∀ i j, K i j = K j i)
          ∧ ∀ v : Mode → ℝ, 0 ≤ ∑ i : Mode, ∑ j : Mode, v i * K i j * v j) := by
  constructor
  · -- A Gram kernel is symmetric and positive semidefinite.
    rintro ⟨m, f, hf⟩
    refine ⟨fun i j => ?_, fun v => ?_⟩
    · rw [← hf i j, ← hf j i, gram_comm]
    · simpa only [hf] using Work.BoseB4.GramQuadForm f v
  · -- A symmetric positive semidefinite kernel is a Gram kernel: factor `Matrix.of K`.
    rintro ⟨hsym, hquad⟩
    have hpsd : (Matrix.of K).PosSemidef := Work.BoseB4.PosSemidefOfQuadform K hsym hquad
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hpsd.nonneg
    refine ⟨Fintype.card Mode, fun i l => B i ((Fintype.equivFin Mode).symm l), fun i j => ?_⟩
    rw [Work.BoseB4.gram]
    calc ∑ l : Fin (Fintype.card Mode),
            B i ((Fintype.equivFin Mode).symm l) * B j ((Fintype.equivFin Mode).symm l)
        = ∑ k : Mode, B i k * B j k :=
          Equiv.sum_comp (Fintype.equivFin Mode).symm (fun k => B i k * B j k)
      _ = (B * star B) i j := by
            rw [Matrix.mul_apply]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial]
      _ = K i j := by
            rw [← hB]
            exact Matrix.of_apply K i j

end Work.BoseB4
