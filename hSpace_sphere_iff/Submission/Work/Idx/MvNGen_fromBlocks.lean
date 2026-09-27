import Mathlib
import Submission.Work.Idx.WPenAppendDefs

namespace Work.Idx

/-- **The `(P 0; C 0)` projection is Murray–von Neumann equivalent to `P`.** If
`X = fromBlocks20 P C = (P 0; C 0)` is idempotent then the blocks of
`X * X` give `P * P = P` and `C * P = C`, and the entry map `a = (P | 0)`
(a `Matrix ι (ι ⊕ κ)`) and the exit map `b = (P ; C)` (stacked, a `Matrix (ι ⊕ κ) ι`) satisfy
`a * b = P` and `b * a = X` (use `Matrix.mul_apply`, `Fintype.sum_sum_type` and the
`fromBlocks20_apply_*` simplification rules). -/
theorem MvNGen_fromBlocks {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix ι ι R) (C : Matrix κ ι R)
    (hP : P * P = P)
    (hX : Work.Idx.fromBlocks20 P C * Work.Idx.fromBlocks20 P C = Work.Idx.fromBlocks20 P C) :
    Work.Idx.MvNGen (Work.Idx.fromBlocks20 P C) P := by
  -- The `(inr, inl)` block of `X * X = X` reads `C * P = C`.
  have hCP : C * P = C := by
    have hX2 : fromBlocks20 P C * fromBlocks20 P C
        = Matrix.fromBlocks (P * P) (0 : Matrix ι κ R) (C * P) (0 : Matrix κ κ R) := by
      simp only [fromBlocks20, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
        add_zero]
    have hblock : Matrix.fromBlocks (P * P) (0 : Matrix ι κ R) (C * P) (0 : Matrix κ κ R)
        = Matrix.fromBlocks P (0 : Matrix ι κ R) C (0 : Matrix κ κ R) := by
      rw [← hX2]; exact hX
    ext k j
    have h := congrFun (congrFun hblock (Sum.inr k)) (Sum.inl j)
    simpa [fromBlocks20] using h
  -- The entry map `a = (P | 0)` and the exit map `b = (P ; C)`.
  let a : Matrix ι (ι ⊕ κ) R := fun i x => Sum.elim (fun j => P i j) (fun _ => (0 : R)) x
  let b : Matrix (ι ⊕ κ) ι R := fun x j => Sum.elim (fun i => P i j) (fun k => C k j) x
  refine ⟨a, b, ?_, ?_⟩
  · ext x y
    cases x <;> cases y
    · rw [Matrix.mul_apply]; simp [a, b, fromBlocks20]; rw [← Matrix.mul_apply, hP]
    · rw [Matrix.mul_apply]; simp [a, b, fromBlocks20, Matrix.fromBlocks_apply₁₂]
    · rw [Matrix.mul_apply]; simp [a, b, fromBlocks20]; rw [← Matrix.mul_apply, hCP]
    · rw [Matrix.mul_apply]; simp [a, b, fromBlocks20, Matrix.fromBlocks_apply₂₂]
  · ext i j
    rw [Matrix.mul_apply]
    simp only [Fintype.sum_sum_type, a, b, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_eq_zero (fun k _ => zero_mul (C k j)), add_zero, ← Matrix.mul_apply, hP]

end Work.Idx
