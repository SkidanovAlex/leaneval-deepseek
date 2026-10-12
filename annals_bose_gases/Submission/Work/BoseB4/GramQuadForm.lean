import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB4.ModeFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.GramQuadForm` — the Gram matrix `(i,j) ↦ gram (f i) (f j)` is
positive semidefinite

`Work.BoseB4.gram f g = Σ_l f_l g_l` is the inner product of the coordinate
vectors `f g : Fin m → ℝ`, so the kernel `K i j = gram (f i) (f j)` of a family
`f : Mode → Fin m → ℝ` is a Gram matrix and hence positive semidefinite:

`Σ_i Σ_j v i * gram (f i) (f j) * v j ≥ 0`.

This is the elementary bilinear-form version of `Matrix.posSemidef_gram`
(`Mathlib.Analysis.InnerProductSpace.GramMatrix`), stated for the coordinate
model of `Work.BoseB4.ModeFock`.  The proof is the square completion
`Σ_i Σ_j v i * gram (f i) (f j) * v j = Σ_l (Σ_i v i * f i l)² ≥ 0`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-- Square completion for the Gram quadratic form: the double sum over the
kernel `gram (f i) (f j)` is the sum of squares of the `l`-th "coordinates" of
the linear combination `Σ_i v i • f i`. -/
lemma gram_quadForm_eq_sum_sq {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    {m : ℕ} (f : Mode → Fin m → ℝ) (v : Mode → ℝ) :
    ∑ i : Mode, ∑ j : Mode, v i * gram (f i) (f j) * v j
      = ∑ l : Fin m, (∑ i : Mode, v i * f i l) ^ 2 := by
  have distrib : ∀ i j : Mode,
      v i * gram (f i) (f j) * v j = ∑ l : Fin m, v i * (f i l * f j l) * v j := by
    intro i j
    rw [gram, Finset.mul_sum, Finset.sum_mul]
  have step1 : ∀ i : Mode,
      (∑ j : Mode, ∑ l : Fin m, v i * (f i l * f j l) * v j)
        = ∑ l : Fin m, ∑ j : Mode, v i * (f i l * f j l) * v j := by
    intro i
    exact Finset.sum_comm
  simp_rw [distrib, step1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem GramQuadForm {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    {m : ℕ} (f : Mode → Fin m → ℝ) (v : Mode → ℝ) :
    0 ≤ ∑ i : Mode, ∑ j : Mode, v i * Work.BoseB4.gram (f i) (f j) * v j := by
  rw [gram_quadForm_eq_sum_sq]
  exact Finset.sum_nonneg fun l _ => sq_nonneg _

end Work.BoseB4
