import Mathlib
import Submission.Work.Certificates.Sparse
import Submission.Work.Certificates.SVec.toFun_flatten
import Submission.Work.Certificates.SVec.toFun_map_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Soundness of sparse composition: `toMatrix (mul A B) = toMatrix A * toMatrix B`

`SOp.mul A B` is sparse composition, computed on the sparse data as
`(A.mul B).img j = A.apply (B.img j)`.  Its matrix is the product of the matrices, i.e. the
sparse composition implements matrix multiplication.

The mathematical content is the distributive law relating the two ways of summing the
coefficients of a list: summing `g p.1 * p.2` over the pairs `p` of a sparse vector `v` is the
same as first collecting, for each index `k`, the total coefficient `v.toFun k` and then
summing `v.toFun k * g k` over `k`.  This is `SVec.sum_map_mul_toFun` below; the rest is
bookkeeping on `List.map`/`List.flatten`.
-/

namespace Work.Certificates

namespace SVec

/-- Pointwise form of `toFun` on a cons: the contribution of the head plus the tail. -/
theorem toFun_cons_apply {n : ℕ} (p : Fin n × ℤ) (l : SVec n) (i : Fin n) :
    toFun (p :: l) i = (if p.1 = i then p.2 else 0) + l.toFun i := by
  simp [toFun]

/-- Summation against a sparse vector: summing `g p.1 * p.2` over the pairs of `v` is the same
as summing `v.toFun k * g k` over the indices `k`, because `v.toFun k` is exactly the total
coefficient of the pairs of `v` carrying the index `k`. -/
theorem sum_map_mul_toFun {n : ℕ} (v : SVec n) (g : Fin n → ℤ) :
    (v.map (fun p => p.2 * g p.1)).sum = ∑ k : Fin n, v.toFun k * g k := by
  induction v with
  | nil => simp [toFun]
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih]
    have hsingle : ∑ k : Fin n, (if p.1 = k then p.2 else 0) * g k = p.2 * g p.1 := by
      rw [Finset.sum_eq_single p.1
        (fun b _ hb => by
          have h : ¬ (p.1 = b) := fun h => hb h.symm
          simp [h])
        (fun h => absurd (Finset.mem_univ p.1) h)]
      simp
    simp only [toFun_cons_apply, add_mul, Finset.sum_add_distrib, hsingle]

end SVec

namespace SOp

/-- A pointwise sum of a family of functions is computed pointwise. -/
private theorem sum_map_apply {n m : ℕ} (v : SVec m) (F : Fin m × ℤ → Fin n → ℤ) (i : Fin n) :
    ((v.map F).sum) i = (v.map (fun p => F p i)).sum := by
  induction v with
  | nil => simp
  | cons p ps ih => simp [List.sum_cons, ih]

/-- Semantics of sparse application: `A.apply` is the linear map with matrix `toMatrix A`, i.e.
`(A.apply v).toFun i = ∑_k (A.img k).toFun i * v.toFun k`. -/
theorem toFun_apply {n m : ℕ} (A : SOp n m) (v : SVec m) (i : Fin n) :
    (A.apply v).toFun i = ∑ k : Fin m, (A.img k).toFun i * v.toFun k := by
  have h1 : (A.apply v).toFun = (v.map (fun p => p.2 • (A.img p.1).toFun)).sum := by
    rw [show A.apply v
        = (v.map (fun p => (A.img p.1).map (fun q => (q.1, q.2 * p.2)))).flatten from rfl]
    rw [SVec.toFun_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    exact SVec.toFun_map_mul (A.img p.1) p.2
  rw [h1, sum_map_apply v (fun p => p.2 • (A.img p.1).toFun) i]
  trans (v.map (fun p => p.2 * (A.img p.1).toFun i)).sum
  · rw [List.map_congr_left (l := v) (f := fun p => (p.2 • (A.img p.1).toFun) i)
      (g := fun p => p.2 * (A.img p.1).toFun i)
      (fun p _ => by simp only [Pi.smul_apply, smul_eq_mul])]
  · rw [SVec.sum_map_mul_toFun v (fun k : Fin m => (A.img k).toFun i)]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- `toMatrix` turns sparse composition of operators into multiplication of matrices. -/
theorem toMatrix_mul {n m l : ℕ} (A : SOp n m) (B : SOp m l) :
    toMatrix (mul A B) = toMatrix A * toMatrix B := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [SOp.toMatrix, SOp.mul]
  exact toFun_apply A (B.img j) i

end SOp

end Work.Certificates
