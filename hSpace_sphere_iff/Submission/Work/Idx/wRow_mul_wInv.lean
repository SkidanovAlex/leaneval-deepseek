import Mathlib
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.WPenRes

namespace Work.Idx

open Matrix

/-- **The coefficient row annihilates the explicit inverse of the W pencil.**
Multiplying the block row `wRow n D c` (whose `k`-th block is `c k`) by the explicit inverse
`wInv n D c z E` of the pencil `z • wBA + wBB` leaves only the last block column: the result is
the block row whose `j`-th block is `1` if `j` is the last index and `0` otherwise. -/
lemma wRow_mul_wInv {A : Type*} [CommRing A] [Algebra ℂ A] (n D : ℕ)
    (c : Fin (D + 1) → Matrix (Fin n) (Fin n) A) (z : ℂ) {E : Matrix (Fin n) (Fin n) A}
    (hE : wQ n D c z * E = 1) :
    wRow n D c * wInv n D c z E
      = wRow n D (fun j : Fin (D + 1) => if (j : ℕ) = D then (1 : Matrix (Fin n) (Fin n) A) else 0) := by
  ext a q
  obtain ⟨i, b⟩ := q
  show (∑ p : Fin (D + 1) × Fin n, wRow n D c a p * wInv n D c z E p (i, b))
      = wRow n D (fun j => if (j : ℕ) = D then (1 : Matrix (Fin n) (Fin n) A) else 0) a (i, b)
  rw [Fintype.sum_prod_type]
  have h1 : ∀ k : Fin (D + 1),
      (∑ a' : Fin n, wRow n D c a (k, a') * wInv n D c z E (k, a') (i, b))
        = (c k * bInv n D c z E k i) a b := by
    intro k
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [wRow]
    show c k a a' * blkOf (wInv n D c z E) k i a' b = c k a a' * bInv n D c z E k i a' b
    rw [blkOf_wInv]
  rw [Finset.sum_congr rfl fun k _ => h1 k, ← Matrix.sum_apply, sum_c_mul_bInv n D c z hE i]
  simp [wRow]

end Work.Idx
