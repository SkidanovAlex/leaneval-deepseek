import Mathlib

/-!
# `Work.KT.whitehead_block_algebra`

The block-matrix identity behind Whitehead's lemma (`Work.KT.whitehead_diag`): if `U` and `V` are
mutually inverse `n × n` matrices over a ring `R`, then

  `[[1,0],[V,1]] · ([[1,-U],[0,1]] · ([[1,1],[0,1]] · ([[1,0],[-1,1]] · [[1,1-V],[0,1]])))
     = [[U,0],[0,V]]`,

i.e. `diag(U,V)` is a product of elementary block matrices.

The computation, block by block (each a plain `Matrix.fromBlocks_multiply`):

* `[[1,0],[-1,1]] · [[1,1-V],[0,1]] = [[1,1-V],[-1,V]]`
* `[[1,1],[0,1]] · [[1,1-V],[-1,V]] = [[0,1],[-1,V]]`
* `[[1,-U],[0,1]] · [[0,1],[-1,V]] = [[U,0],[-1,V]]`   (uses `U * V = 1`)
* `[[1,0],[V,1]] · [[U,0],[-1,V]] = [[U,0],[0,V]]`     (uses `V * U = 1`)

Lean performs all four block multiplications at once and then discharges the four resulting
(noncommutative) ring identities with `simp`, using `U * V = 1` and `V * U = 1`.
-/

namespace Work.KT

theorem whitehead_block_algebra {R : Type} [Ring R] {n : ℕ} (U V : Matrix (Fin n) (Fin n) R)
    (hVU : V * U = 1) (hUV : U * V = 1) :
    (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 V 1 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) *
      ((Matrix.fromBlocks 1 (-U) 0 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) *
        ((Matrix.fromBlocks 1 1 0 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) *
          ((Matrix.fromBlocks 1 0 (-1) 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) *
            (Matrix.fromBlocks 1 (1 - V) 0 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R))))
      = (Matrix.fromBlocks U 0 0 V : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hUV, hVU]

end Work.KT
