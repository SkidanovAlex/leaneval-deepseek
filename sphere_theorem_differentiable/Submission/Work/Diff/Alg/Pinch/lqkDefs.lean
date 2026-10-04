import Mathlib
import Submission.Work.Diff.Alg.Pinch.BQDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary `2`-tensor algebra for the Böhm–Wilking identity on `A ∧ id`

Helper definitions used in `Work.Diff.Alg.Pinch.linv_Q_ell_knProd`: the matrix square `sqT A`,
the trace `trT A` and the squared Frobenius norm `frobT A` of a `2`-tensor
`A : Fin n → Fin n → ℝ`.
-/

namespace Work.Diff.Alg.Pinch

variable {n : ℕ}

/-- The square of a `2`-tensor: `sqT A i j = ∑ k, A i k * A k j`. -/
noncomputable def sqT (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k, A i k * A k j

/-- The trace of a `2`-tensor. -/
noncomputable def trT (A : Fin n → Fin n → ℝ) : ℝ := ∑ i, A i i

/-- The squared Frobenius norm of a `2`-tensor. -/
noncomputable def frobT (A : Fin n → Fin n → ℝ) : ℝ := ∑ i, ∑ j, A i j * A i j

@[simp] lemma sqT_apply (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    sqT A i j = ∑ k, A i k * A k j := rfl

@[simp] lemma trT_apply (A : Fin n → Fin n → ℝ) : trT A = ∑ i, A i i := rfl

@[simp] lemma frobT_apply (A : Fin n → Fin n → ℝ) :
    frobT A = ∑ i, ∑ j, A i j * A i j := rfl

end Work.Diff.Alg.Pinch
