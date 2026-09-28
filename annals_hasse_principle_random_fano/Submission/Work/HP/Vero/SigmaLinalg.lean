import Mathlib
import Submission.Work.HP.Vero.SigmaDefs

/-!
# The symmetric matrix attached to a degree-two coefficient vector

For `a : Mon 2 n → ℝ` we let `matA n a` be the symmetric `(n+1) × (n+1)` matrix with entries
`matA n a i j = a (pairMon n i j)`, i.e. the coefficient of `XᵢXⱼ` in the quadratic form `f_a`.

The basic identity relating this matrix with `σ` is
`∑ m, a m * σ(u,v) m = ∑ i, ∑ j, matA n a i j * u i * v j`
(see `Work.HP.Vero.dot_sigma_single_real` and the main file), so that `matA` is the matrix of the
symmetric bilinear form associated with `f_a`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Vero

/-- `pairMon` is symmetric in its two indices: `XᵢXⱼ = XⱼXᵢ`. -/
lemma pairMon_comm (n : ℕ) (i j : Fin (n + 1)) : pairMon n i j = pairMon n j i := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  simp only [pairMon, Work.HP.NA.monDij, Fin.val_mk]
  rw [Nat.add_comm]

/-- The symmetric matrix of a degree-two coefficient vector: `matA a i j = a (Xᵢ Xⱼ)`. -/
def matA (n : ℕ) (a : Mon 2 n → ℝ) : Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => a (pairMon n i j)

@[simp] lemma matA_apply (n : ℕ) (a : Mon 2 n → ℝ) (i j : Fin (n + 1)) :
    matA n a i j = a (pairMon n i j) := rfl

/-- `matA n a` is symmetric. -/
lemma matA_comm (n : ℕ) (a : Mon 2 n → ℝ) (i j : Fin (n + 1)) :
    matA n a i j = matA n a j i := by
  simp only [matA_apply, pairMon_comm]

end Work.HP.Vero
