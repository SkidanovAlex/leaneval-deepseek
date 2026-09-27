import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Clutch

/-!
# `Work.KT.Fund.OrthProjAlg` — elementary algebra of the orthogonal projection `orthProj`

For a `2n × n` matrix `B` over a commutative star-ring whose Gram matrix `Bᴴ B` is a unit,
`orthProj R B = B (BᴴB)⁻¹ Bᴴ` is an idempotent which fixes the image of `B`.
-/

namespace Work.KT.Fund

open Matrix

theorem orthProj_mul_self {n : ℕ} (R : Type) [CommRing R] [StarRing R]
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) (h : IsUnit (Matrix.conjTranspose B * B)) :
    orthProj R B * orthProj R B = orthProj R B := by
  have hQinv : Ring.inverse (Matrix.conjTranspose B * B) * (Matrix.conjTranspose B * B) = 1 :=
    Ring.inverse_mul_cancel _ h
  simp only [orthProj]
  calc B * Ring.inverse (Bᴴ * B) * Bᴴ * (B * Ring.inverse (Bᴴ * B) * Bᴴ)
      = B * Ring.inverse (Bᴴ * B) * (Bᴴ * B) * Ring.inverse (Bᴴ * B) * Bᴴ := by
        simp only [Matrix.mul_assoc]
    _ = B * (Ring.inverse (Bᴴ * B) * (Bᴴ * B)) * Ring.inverse (Bᴴ * B) * Bᴴ := by
        simp only [Matrix.mul_assoc]
    _ = B * Ring.inverse (Bᴴ * B) * Bᴴ := by
        rw [hQinv]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem orthProj_mul_apply {n : ℕ} (R : Type) [CommRing R] [StarRing R]
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) (h : IsUnit (Matrix.conjTranspose B * B)) :
    orthProj R B * B = B := by
  have hQinv : Ring.inverse (Matrix.conjTranspose B * B) * (Matrix.conjTranspose B * B) = 1 :=
    Ring.inverse_mul_cancel _ h
  simp only [orthProj]
  calc B * Ring.inverse (Bᴴ * B) * Bᴴ * B
      = B * Ring.inverse (Bᴴ * B) * (Bᴴ * B) := by simp only [Matrix.mul_assoc]
    _ = B * (Ring.inverse (Bᴴ * B) * (Bᴴ * B)) := by simp only [Matrix.mul_assoc]
    _ = B := by rw [hQinv, Matrix.mul_one]

end Work.KT.Fund
