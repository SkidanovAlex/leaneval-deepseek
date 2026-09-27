import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.Idx.WPenRes

/-!
# `Work.KT.FP.wPen_isUnit_of_sum_isUnit`

The W linearisation of a polynomial clutching function is invertible wherever the polynomial is.

For a coefficient sequence `b : Fin (d+1) → Mₙ(C(X, ℂ))` with polynomial matrix
`Q(z) = ∑_j z^j • b_j`, the companion pencil `W(z) = z • wPenA + wPenB b` satisfies

* `isUnit_blockPencil_of_isUnit_sum` : `IsUnit (Q z) → IsUnit (W z)`, over an arbitrary
  commutative `ℂ`-algebra (this is `Work.Idx.wBlk_mul_wInv` + the determinant criterion);
* `wPen_isUnit_of_sum_isUnit` : the same statement for the reindexed `wPenAf`/`wPenBf` on
  `Fin ((d+1) * n)`, which is the form used by `matPProj`.

The mathematical content is the explicit block inverse of the pencil: writing `v = (v_0, …, v_d)`,
the equations `W(z) v = y` read `z v_i - v_{i+1} = y_i` for `i < d` and `∑_j b_j v_j = y_d`, so
`v_i = z^i v_0 - ∑_{k<i} z^{i-1-k} y_k` and `Q(z) v_0 = y_d + ∑_{k<d} (∑_{j>k} z^{j-1-k} b_j) y_k`;
hence `W(z)` is invertible as soon as `Q(z)` is. (No hypothesis on `z` is needed: the recursion
never divides by `z`, so the statement also holds at `z = 0`.)
-/

namespace Work.KT.FP

open Matrix

noncomputable section

/-- **The W pencil is a unit wherever its polynomial is.**  For a commutative `ℂ`-algebra `A`, if
the polynomial matrix `Q(z) = ∑_j z^j • b_j` of the coefficient sequence `b` is invertible in
`Mₙ(A)`, then so is the companion pencil `z • wBA + wBB b`. -/
theorem isUnit_blockPencil_of_isUnit_sum {A : Type*} [CommRing A] [Algebra ℂ A]
    {n d : ℕ} (b : Fin (d + 1) → Matrix (Fin n) (Fin n) A) {z : ℂ}
    (h : IsUnit (∑ j : Fin (d + 1), z ^ (j : ℕ) • b j)) :
    IsUnit (z • Work.Idx.wBA n d + Work.Idx.wBB n d b) := by
  have hQ : IsUnit (Work.Idx.wQ n d b z) := h
  have hE : Work.Idx.wQ n d b z * Ring.inverse (Work.Idx.wQ n d b z) = 1 :=
    Ring.mul_inverse_cancel _ hQ
  have hmul := Work.Idx.wBlk_mul_wInv n d b z hE
  have hdet : (z • Work.Idx.wBA n d + Work.Idx.wBB n d b).det *
      (Work.Idx.wInv n d b z (Ring.inverse (Work.Idx.wQ n d b z))).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  rw [Matrix.isUnit_iff_isUnit_det]
  exact ⟨⟨_, _, hdet, by rw [mul_comm, hdet]⟩, rfl⟩

/-- **Invertibility of the W linearisation, reindexed.**  If the polynomial matrix carried by the
coefficient sequence `b` is invertible at `z`, then so is the W pencil `z • wPenAf + wPenBf` on the
index type `Fin ((d+1) * n)`. -/
theorem wPen_isUnit_of_sum_isUnit (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) {z : ℂ} (hz : z ≠ 0)
    (h : IsUnit (∑ j : Fin (d + 1), z ^ (j : ℕ) • b j)) :
    IsUnit (z • wPenAf X n d + wPenBf X n d b) := by
  have hblk : IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b) :=
    isUnit_blockPencil_of_isUnit_sum b h
  have hkey : z • wPenAf X n d + wPenBf X n d b
      = Matrix.reindex finProdFinEquiv finProdFinEquiv
          (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b) := by
    simp only [wPenAf, wPenBf, Matrix.reindex_apply, Matrix.submatrix_add, Matrix.submatrix_smul,
      Pi.add_apply, Pi.smul_apply]
    rfl
  rw [hkey]
  exact hblk.map (Matrix.reindexRingEquiv C(X, ℂ) finProdFinEquiv)

end

end Work.KT.FP
