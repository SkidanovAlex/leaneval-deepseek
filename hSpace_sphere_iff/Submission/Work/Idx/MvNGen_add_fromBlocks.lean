import Mathlib
import Submission.Work.Idx.WPenAppendDefs

namespace Work.Idx

/-- **A sum of orthogonal idempotents is Murray–von Neumann equivalent to the block sum.**

`MvNGen p q` (from `Submission/Work/Idx/WPenAppendDefs.lean`) is Murray–von Neumann equivalence of
square matrices on arbitrary finite index types: `∃ a : Matrix ι₂ ι₁ R, ∃ b : Matrix ι₁ ι₂ R,
b * a = p ∧ a * b = q`.  Claim: for idempotents `e f : Matrix ι ι R` with `e * f = f * e = 0`,
the idempotent `e + f` is MvN equivalent to the block diagonal matrix `fromBlocks e 0 0 f` (on
`ι ⊕ ι`).

Witnesses: `a : Matrix (ι ⊕ ι) ι` with `a (Sum.inl i) j = e i j`, `a (Sum.inr i) j = f i j`,
and `b : Matrix ι (ι ⊕ ι)` with `b i (Sum.inl j) = e i j`, `b i (Sum.inr j) = f i j`.  Then
`b * a = e * e + f * f = e + f` (`Matrix.mul_apply`, `Fintype.sum_sum_type`), and the four blocks
of `a * b` are `e * e = e`, `e * f = 0`, `f * e = 0`, `f * f = f`. -/
theorem MvNGen_add_fromBlocks {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e f : Matrix ι ι R) (he : e * e = e) (hf : f * f = f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    Work.Idx.MvNGen (e + f) (Matrix.fromBlocks e (0 : Matrix ι ι R) (0 : Matrix ι ι R) f) := by
  -- the entry map `a` stacks `e` over `f`; the exit map `b` places them side by side
  let a : Matrix (ι ⊕ ι) ι R := fun i j => Sum.elim (fun x => e x j) (fun y => f y j) i
  let b : Matrix ι (ι ⊕ ι) R := fun i j => Sum.elim (fun x => e i x) (fun y => f i y) j
  refine ⟨a, b, ?_, ?_⟩
  · -- `b * a = e * e + f * f = e + f`
    ext i j
    rw [Matrix.mul_apply]
    simp only [Fintype.sum_sum_type, a, b, Sum.elim_inl, Sum.elim_inr]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, he, hf]
    rfl
  · -- the four blocks of `a * b` are `e`, `0`, `0`, `f`
    ext i j
    cases i <;> cases j
    · rw [Matrix.mul_apply]
      simp only [a, b, Sum.elim_inl, Matrix.fromBlocks_apply₁₁]
      rw [← Matrix.mul_apply, he]
    · rw [Matrix.mul_apply]
      simp only [a, b, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂]
      rw [← Matrix.mul_apply, hef]
    · rw [Matrix.mul_apply]
      simp only [a, b, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁]
      rw [← Matrix.mul_apply, hfe]
    · rw [Matrix.mul_apply]
      simp only [a, b, Sum.elim_inr, Matrix.fromBlocks_apply₂₂]
      rw [← Matrix.mul_apply, hf]

end Work.Idx
