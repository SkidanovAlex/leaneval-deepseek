import Mathlib
import Submission.Work.KT.Fund.Clutch

namespace Work.KT.Fund

/-- `star` of the `0/1`-valued `if`, used in reducing the Gram matrices of the block columns. -/
private lemma star_ite_one_zero {R : Type} [Ring R] [StarRing R] (P : Prop) [Decidable P] :
    star (if P then (1 : R) else 0) = if P then 1 else 0 := by
  split <;> simp

theorem graphB_recipB_conjTranspose_mul_self {n : ℕ} (R : Type) [CommRing R] [StarRing R]
    (F G : Matrix (Fin n) (Fin n) R) :
    (Work.KT.Fund.graphB R F).conjTranspose * Work.KT.Fund.graphB R F = 1 + F.conjTranspose * F ∧
    (Work.KT.Fund.recipB R G).conjTranspose * Work.KT.Fund.recipB R G = 1 + G.conjTranspose * G := by
  constructor
  · ext j k
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
      Work.KT.Fund.graphB, Fintype.sum_sum_type, Matrix.one_apply]
    simp only [star_ite_one_zero]
    simp [eq_comm]
  · ext j k
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
      Work.KT.Fund.recipB, Fintype.sum_sum_type, Matrix.one_apply]
    simp only [star_ite_one_zero]
    simp [eq_comm]
    exact add_comm _ _

end Work.KT.Fund
