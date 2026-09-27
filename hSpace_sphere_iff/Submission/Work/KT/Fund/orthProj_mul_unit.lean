import Mathlib
import Submission.Work.KT.Fund.Clutch

/-!
# `orthProj` is invariant under right multiplication by a unit

The orthogonal projection onto the image of a `2n × n` matrix `B` (with respect to the standard
Hermitian form), namely `B * (BᴴB)⁻¹ * Bᴴ`, depends only on the *image* of `B`.  Hence
multiplying `B` on the right by an invertible `n × n` matrix `M` does not change it.

The proof is a computation with `Ring.inverse` (the totalized inverse).  Writing `N = Mᴴ` and
`Q = BᴴB`, one has `(BM)ᴴ(BM) = N Q M`, and since `M` and `N` are units the totalized inverse
satisfies `Ring.inverse (N Q M) = Ring.inverse M * Ring.inverse Q * Ring.inverse N`.  The two
unit factors then cancel against the outer `BM` and `N` factors.
-/

namespace Work.KT.Fund

open Matrix

theorem orthProj_mul_unit {n : ℕ} (R : Type) [CommRing R] [StarRing R]
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) (M : Matrix (Fin n) (Fin n) R) (hM : IsUnit M) :
    Work.KT.Fund.orthProj R (B * M) = Work.KT.Fund.orthProj R B := by
  -- `Mᴴ` is again a unit.
  have hN : IsUnit (Mᴴ) := (Matrix.isUnit_conjTranspose M).2 hM
  -- The totalized inverse of `(BM)ᴴ(BM) = Mᴴ (BᴴB) M` splits as `(M⁻¹ʳ) * (BᴴB)⁻¹ʳ * (Mᴴ)⁻¹ʳ`.
  have h1 : Ring.inverse ((B * M)ᴴ * (B * M))
      = (Ring.inverse M * Ring.inverse (Bᴴ * B)) * Ring.inverse (Mᴴ) := by
    rw [Matrix.conjTranspose_mul]
    rw [Matrix.mul_assoc (Mᴴ) Bᴴ (B * M), ← Matrix.mul_assoc Bᴴ B M]
    rw [Ring.inverse_mul (Or.inl hN), Ring.inverse_mul (Or.inr hM)]
  simp only [Work.KT.Fund.orthProj]
  rw [h1, Matrix.conjTranspose_mul]
  -- Reassociate and cancel the two unit factors.
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Ring.inverse (Mᴴ)) (Mᴴ) Bᴴ, Ring.inverse_mul_cancel (Mᴴ) hN,
    Matrix.one_mul]
  rw [← Matrix.mul_assoc M (Ring.inverse M) (Ring.inverse (Bᴴ * B) * Bᴴ),
    Ring.mul_inverse_cancel M hM, Matrix.one_mul]

end Work.KT.Fund
