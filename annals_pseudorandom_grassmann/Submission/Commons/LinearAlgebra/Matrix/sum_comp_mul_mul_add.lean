import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.card_fiber_mul_mul_add

namespace Commons.LinearAlgebra.Matrix

theorem sum_comp_mul_mul_add {m n m' n' : ℕ} {M : Type*} [AddCommMonoid M]
    (Q : Matrix (Fin n') (Fin n) (ZMod 2)) (ι : Matrix (Fin m) (Fin m') (ZMod 2))
    (hQ : Function.Injective Q.mulVecLin) (hι : Function.Surjective ι.mulVecLin)
    (T : Matrix (Fin m) (Fin n) (ZMod 2)) (g : Matrix (Fin m) (Fin n) (ZMod 2) → M) :
    ∑ A : Matrix (Fin m') (Fin n') (ZMod 2), g (ι * A * Q + T) =
      (2 ^ (m' * n' - m * n)) • ∑ B : Matrix (Fin m) (Fin n) (ZMod 2), g B := by
  classical
  rw [← Finset.sum_fiberwise' (Finset.univ : Finset (Matrix (Fin m') (Fin n') (ZMod 2)))
        (fun A => ι * A * Q + T) g]
  have hinner : ∀ B : Matrix (Fin m) (Fin n) (ZMod 2),
      (∑ A ∈ (Finset.univ : Finset (Matrix (Fin m') (Fin n') (ZMod 2))) with
        ι * A * Q + T = B, g B) = 2 ^ (m' * n' - m * n) • g B := by
    intro B
    rw [Finset.sum_const]
    congr 1
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_fiber_mul_mul_add Q ι hQ hι T B
  simp only [hinner]
  rw [Finset.smul_sum]

end Commons.LinearAlgebra.Matrix
