import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.isStarRegular_of_ringEquiv
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix

/-!
# Positive definite ⋆-regular rings are closed under matrix rings

If `U` is positive definite ⋆-regular (i.e. `Mat_k(U)` is ⋆-regular for every `k`), then so is
`Mat_n(U)`: for `Mat_n(U)` this says that `Mat_m(Mat_n(U))` is ⋆-regular for every `m`, and
`Mat_m(Mat_n(U))` is carried to `Mat_{m n}(U)` -- ⋆-regular by hypothesis -- by the block
flattening isomorphism

`Mat_m(Mat_n(U)) ≃ Mat_{m × n}(Mat_{m × n}(U)) ≃ Mat_{m n}(U)`,

which respects the conjugate-transpose involution on both sides.
-/

namespace Work.ORHughesFree.StarRegular

open Matrix

universe u

/-- The block flattening ring equivalence
`Mat_m(Mat_n(R)) ≃+* Mat_{m × n}(R)`: it sends `A` to the matrix `(p, q) ↦ A p.1 q.1 p.2 q.2`. -/
private noncomputable def matrixBlockEquiv (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (R : Type*) [Ring R] :
    Matrix m m (Matrix n n R) ≃+* Matrix (m × n) (m × n) R where
  toFun A := Matrix.of fun (p q : m × n) => A p.1 q.1 p.2 q.2
  invFun B := Matrix.of fun (i j : m) => Matrix.of fun (a b : n) => B (i, a) (j, b)
  left_inv A := by funext i j a b; rfl
  right_inv B := by funext p q; rcases p with ⟨i, a⟩; rcases q with ⟨j, b⟩; rfl
  map_add' A B := by ext p q; rfl
  map_mul' A B := by
    ext p q
    rcases p with ⟨i, a⟩
    rcases q with ⟨j, b⟩
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]

/-- The block flattening equivalence is compatible with the conjugate-transpose involutions. -/
private lemma matrixBlockEquiv_star {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (R : Type*) [Ring R] [StarRing R] (A : Matrix m m (Matrix n n R)) :
    matrixBlockEquiv m n R (star A) = star (matrixBlockEquiv m n R A) := by
  ext p q
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  rfl

/-- Reindexing a matrix along an equivalence of index types is compatible with the
conjugate-transpose involutions. -/
private lemma reindexRingEquiv_star {m n : Type*} [Fintype m] [Fintype n] (R : Type*) [Ring R]
    [StarRing R] (e : m ≃ n) (A : Matrix m m R) :
    Matrix.reindexRingEquiv R e (star A) = star (Matrix.reindexRingEquiv R e A) := by
  ext i j
  simp only [Matrix.coe_reindexRingEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.star_apply]

/-- The inverse of a ring equivalence compatible with the involutions is again compatible. -/
private lemma starEquiv_symm_star {R S : Type*} [Ring R] [StarRing R] [Ring S] [StarRing S]
    (e : R ≃+* S) (hstar : ∀ x : R, e (star x) = star (e x)) (y : S) :
    e.symm (star y) = star (e.symm y) := by
  refine e.injective ?_
  rw [RingEquiv.apply_symm_apply, hstar, RingEquiv.apply_symm_apply]

theorem isPositiveDefiniteStarRegular_matrix {U : Type u} [Ring U] [StarRing U] (h : IsPositiveDefiniteStarRegular U) (n : ℕ) : IsPositiveDefiniteStarRegular (Matrix (Fin n) (Fin n) U) := by
  intro m
  let e1 := matrixBlockEquiv (Fin m) (Fin n) U
  let e2 := Matrix.reindexRingEquiv U (finProdFinEquiv (m := m) (n := n))
  let E : Matrix (Fin (m * n)) (Fin (m * n)) U ≃+*
      Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) U) := e2.symm.trans e1.symm
  refine isStarRegular_of_ringEquiv E ?_ (h (m * n))
  intro x
  show E (star x) = star (E x)
  simp only [E, RingEquiv.trans_apply]
  rw [starEquiv_symm_star e2 (reindexRingEquiv_star U _)]
  rw [starEquiv_symm_star e1 (matrixBlockEquiv_star U)]

end Work.ORHughesFree.StarRegular
