import Mathlib
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.WPenRes

namespace Work.Idx

open Matrix

/-- The row vector `c̃` with `c_j = 1` at `j = D` and `0` elsewhere annihilates the `z`-coefficient
`wBA` of the W pencil.  The point is that `wBA` is block-diagonal with the identity in every block
except the last, so every surviving term `c_m · (wBA)_{m,q}` carries a factor `c_m` with `m ≠ D`
(hence zero) or is killed by the vanishing of the last block of `wBA`. -/
lemma wRow_delta_mul_wBA {A : Type*} [CommRing A] [Algebra ℂ A] (n D : ℕ) :
    wRow n D (fun j : Fin (D + 1) => if (j : ℕ) = D then (1 : Matrix (Fin n) (Fin n) A) else 0)
      * wBA (A := A) n D = 0 := by
  ext p q
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases h : (m.1 : ℕ) = D
  · have hb : wBA (A := A) n D m q = 0 := by
      simp only [wBA]
      simp [h]
    simp [wRow, hb]
  · simp only [wRow, wBA]
    simp [h]

end Work.Idx
