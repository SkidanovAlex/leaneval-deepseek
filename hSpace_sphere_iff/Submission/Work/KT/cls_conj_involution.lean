import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic

namespace Work.KT

open Matrix

/-- Conjugation by an involution `W` (`W * W = 1`) preserves the `K₀` class of an idempotent:
`[W * D * W] = [D]`.  Indeed `W * D * W` is Murray–von Neumann equivalent to `D` via the
matrices `D * W` and `W * D`. -/
theorem cls_conj_involution {R : Type} [Ring R] {n : ℕ} {W D : Matrix (Fin n) (Fin n) R}
    (hW : W * W = 1) (hD : D * D = D) :
    cls (⟨n, W * D * W⟩ : Mat R) = cls (⟨n, D⟩ : Mat R) := by
  -- `(W * A * W) * (W * B * W) = W * (A * B) * W` since `W` is an involution.
  have key : ∀ A B : Matrix (Fin n) (Fin n) R,
      (W * A * W) * (W * B * W) = W * (A * B) * W := by
    intro A B
    rw [show (W * A * W) * (W * B * W) = W * A * (W * W) * B * W by noncomm_ring, hW]
    noncomm_ring
  have hp : Mat.IsIdem (⟨n, W * D * W⟩ : Mat R) := by
    show (W * D * W) * (W * D * W) = W * D * W
    rw [key D D, hD]
  have hmv : Mat.MvN (⟨n, W * D * W⟩ : Mat R) (⟨n, D⟩ : Mat R) := by
    refine ⟨D * W, W * D, ?_, ?_⟩
    · show W * D * (D * W) = W * D * W
      rw [show W * D * (D * W) = W * (D * D) * W by noncomm_ring, hD]
    · show D * W * (W * D) = D
      rw [show D * W * (W * D) = D * (W * W) * D by noncomm_ring, hW, mul_one, hD]
  exact cls_eq_of_mvN hp hD hmv

end Work.KT
