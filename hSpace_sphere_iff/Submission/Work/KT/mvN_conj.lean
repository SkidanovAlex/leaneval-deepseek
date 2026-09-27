import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT

/-- For an idempotent `p` and a unit `E`, the conjugated matrix `E⁻¹ p E` is Murray–von Neumann
equivalent to `p`. -/
theorem mvN_conj {R : Type} [Ring R] {n : ℕ} (E : (Matrix (Fin n) (Fin n) R)ˣ)
    (p : Matrix (Fin n) (Fin n) R) (hp : p * p = p) :
    Mat.MvN (⟨n, (↑E⁻¹ : Matrix (Fin n) (Fin n) R) * p * (↑E : Matrix (Fin n) (Fin n) R)⟩ : Mat R)
      ⟨n, p⟩ := by
  refine ⟨(↑E : Matrix (Fin n) (Fin n) R), (↑E⁻¹ : Matrix (Fin n) (Fin n) R) * p, ?_, ?_⟩
  · rfl
  · rw [← mul_assoc, Units.mul_inv, one_mul]

end Work.KT
