import Mathlib
import Submission.Work.KT.Psi.psi2sum_Aux
import Submission.Work.KT.Psi.psi2sum_Setup
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Defs

/-!
# `Work.KT.Psi.sq2Sum_block_mul`

The block form of `ψ²` on a direct sum: multiplying the Kronecker square
`(p ⊕ q) ⊗ (p ⊕ q)` (in its four-block form `psi2sumB`) by the `ε`-projector
`(1 + ε·swap)/2` (in its block form `psi2sumQB`) gives exactly the block matrix
`sqBlock ε p q` of `sq2PartP ε p`, the mixed block `midRaw ε p q` and `sq2PartP ε q`.

The computation is purely structural: `fromBlocks` multiplication distributes over the
(diagonal) block structure, and the only "mixed" entry `p ⊗ q · swap` becomes
`ε · (p ⊗ q)`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-- An `A`-scalar `algebraMap ℂ A c` acts on matrices exactly as the complex scalar `c`. -/
theorem psi2sum_algebraMap_smul {A : Type} [Ring A] [Algebra ℂ A] {ι κ : Type} (c : ℂ)
    (M : Matrix ι κ A) : algebraMap ℂ A c • M = c • M := by
  ext i j
  simp only [Matrix.smul_apply, Algebra.smul_def, smul_eq_mul]

/-- `1 + ε·psi2sumQB` in block form, ready for block multiplication with `psi2sumB`. -/
theorem psi2sum_one_add_smul_QB {A : Type} [Ring A] [Algebra ℂ A] (ε : ℂ) (n m : ℕ) :
    1 + algebraMap ℂ A ε • psi2sumQB A n m =
      Matrix.fromBlocks
        (Matrix.fromBlocks
          (1 + algebraMap ℂ A ε • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n))) 0 0
          (Matrix.fromBlocks (1 : Matrix (Fin n × Fin m) (Fin n × Fin m) A)
            (algebraMap ℂ A ε • relMat A (Equiv.prodComm (Fin n) (Fin m)))
            (algebraMap ℂ A ε • relMat A (Equiv.prodComm (Fin m) (Fin n)))
            (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) A)))
        0 0
        (1 + algebraMap ℂ A ε • Equiv.Perm.permMatrix A (Equiv.prodComm (Fin m) (Fin m))) := by
  rw [psi2sumQB]
  rw [show (1 : Matrix
        (((Fin n × Fin n) ⊕ ((Fin n × Fin m) ⊕ (Fin m × Fin n))) ⊕ (Fin m × Fin m))
        (((Fin n × Fin n) ⊕ ((Fin n × Fin m) ⊕ (Fin m × Fin n))) ⊕ (Fin m × Fin m)) A) =
      Matrix.fromBlocks (Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks 1 0 0 1)) 0 0 1 from by
    rw [Matrix.fromBlocks_one, Matrix.fromBlocks_one, Matrix.fromBlocks_one]]
  simp only [Matrix.fromBlocks_add, Matrix.fromBlocks_smul, smul_zero, add_zero, zero_add]

theorem sq2Sum_block_mul {A : Type} [Ring A] [Algebra ℂ A] {p q : Work.KT.Mat A} (ε : ℂ) :
    Work.KT.Psi.psi2sumB p q *
        (algebraMap ℂ A (1 / 2) • (1 + algebraMap ℂ A ε • Work.KT.Psi.psi2sumQB A p.1 q.1)) =
      Work.KT.Psi.sqBlock ε p q := by
  rw [psi2sum_one_add_smul_QB (A := A) ε p.1 q.1]
  simp only [Work.KT.Psi.psi2sumB, Work.KT.Psi.sqBlock, Work.KT.sq2PartP, Work.KT.Psi.midRaw,
    Work.KT.Psi.kronP, psi2sum_algebraMap_smul, Matrix.fromBlocks_smul, smul_zero]
  rw [Matrix.mul_smul]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_smul, add_zero, zero_add, mul_one, smul_smul,
    Matrix.mul_zero, Matrix.zero_mul, smul_zero]

end

end Work.KT.Psi
