import Mathlib
import Submission.Work.ORHughesFree.MatrixBlocks

namespace Work.ORHughesFree.MatrixBlocks

open Matrix
open Finset

/-- The first component of `finProdFinEquiv (x, y)` is `x`. -/
lemma finProdFinEquiv_fst {l n : ℕ} (x : Fin l) (y : Fin n) :
    (finProdFinEquiv (x, y) : Fin (l * n)).divNat = x := by
  have h := Equiv.symm_apply_apply (finProdFinEquiv (m := l) (n := n)) (x, y)
  rw [finProdFinEquiv_symm_apply] at h
  exact congrArg Prod.fst h

/-- The second component of `finProdFinEquiv (x, y)` is `y`. -/
lemma finProdFinEquiv_snd {l n : ℕ} (x : Fin l) (y : Fin n) :
    (finProdFinEquiv (x, y) : Fin (l * n)).modNat = y := by
  have h := Equiv.symm_apply_apply (finProdFinEquiv (m := l) (n := n)) (x, y)
  rw [finProdFinEquiv_symm_apply] at h
  exact congrArg Prod.snd h

/-- Reindexing a sum over `Fin (l * n)` as a double sum over `Fin l` and `Fin n`,
matching the `divNat`/`modNat` decomposition used by `flattenBlocks`. -/
lemma sum_finProdFin {M : Type*} [AddCommMonoid M] {l n : ℕ} (f : Fin l → Fin n → M) :
    (∑ x : Fin (l * n), f x.divNat x.modNat) = ∑ x : Fin l, ∑ y : Fin n, f x y := by
  rw [← Equiv.sum_comp (finProdFinEquiv (m := l) (n := n)) (fun z => f z.divNat z.modNat)]
  rw [Fintype.sum_prod_type]
  simp only [finProdFinEquiv_fst, finProdFinEquiv_snd]

theorem flattenBlocks_mul {R : Type*} [Ring R] {n k l p : ℕ}
    (A : Matrix (Fin k) (Fin l) (Matrix (Fin n) (Fin n) R))
    (B : Matrix (Fin l) (Fin p) (Matrix (Fin n) (Fin n) R)) :
    flattenBlocks (A * B) = flattenBlocks A * flattenBlocks B := by
  ext i j
  simp only [flattenBlocks, finProdFinEquiv_symm_apply, Matrix.mul_apply, Matrix.sum_apply]
  rw [sum_finProdFin (f := fun x y => A i.divNat x i.modNat y * B x j.divNat y j.modNat)]

end Work.ORHughesFree.MatrixBlocks
