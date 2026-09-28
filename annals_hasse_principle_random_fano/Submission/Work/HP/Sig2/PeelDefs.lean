import Mathlib
import Submission.Work.HP.Sig2.GaussPoissonDefs

/-!
# The peeling reindexing for matrices indexed by `Fin (R+1)`

The purpose of this file is the equivalence

`peelEquiv R : Fin R ⊕ Fin 1 ≃ Fin (R + 1)`,  `Sum.inl i ↦ i.succ`,  `Sum.inr 0 ↦ 0`,

which separates the "head" index `0` of a matrix `G : Matrix (Fin (R+1)) (Fin (R+1)) ℝ` from the
"tail" indices `1, …, R`.  Under `G.submatrix (peelEquiv R) (peelEquiv R)` the matrix `G` becomes
the `2 × 2` block matrix whose leading `R × R` block is the tail `pTail G` and whose trailing
`1 × 1` block is the head `pHead G`; this is the shape in which the Schur complement determinant
formula `Matrix.det_fromBlocks₁₁` applies.
-/

noncomputable section

open Matrix

namespace Work.HP.Sig2

/-- `Fin R ⊕ Fin 1 ≃ Fin (R+1)` sending `Sum.inl i` to `i.succ` and `Sum.inr 0` to `0`. -/
def peelEquiv (R : ℕ) : Fin R ⊕ Fin 1 ≃ Fin (R + 1) where
  toFun := Sum.elim (fun i => Fin.succ i) (fun _ => 0)
  invFun := Fin.cases (Sum.inr 0) (fun i => Sum.inl i)
  left_inv := by
    rintro (i | i)
    · simp
    · fin_cases i; rfl
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl

@[simp] theorem peelEquiv_inl {R : ℕ} (i : Fin R) : peelEquiv R (Sum.inl i) = i.succ := rfl

@[simp] theorem peelEquiv_inr {R : ℕ} (i : Fin 1) : peelEquiv R (Sum.inr i) = 0 := rfl

@[simp] theorem peelEquiv_symm_zero {R : ℕ} : (peelEquiv R).symm 0 = Sum.inr 0 :=
  (peelEquiv R).symm_apply_apply (Sum.inr 0)

@[simp] theorem peelEquiv_symm_succ {R : ℕ} (i : Fin R) :
    (peelEquiv R).symm i.succ = Sum.inl i :=
  (peelEquiv R).symm_apply_apply (Sum.inl i)

end Work.HP.Sig2
