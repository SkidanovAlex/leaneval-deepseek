import Mathlib
import Submission.Work.HP.Vero.MulDefs

namespace Work.HP.Vero

private lemma ite_add_zero {R : Type*} [AddZeroClass R] (c : Prop) [Decidable c] (x y : R) :
    (if c then x + y else 0) = (if c then x else 0) + (if c then y else 0) := by
  by_cases h : c <;> simp [h]

theorem mulVec_add_left {a b d n : ℕ} {R : Type*} [CommSemiring R]
    (A A' : Mon a n → R) (B : Mon b n → R) :
    mulVec a b d (A + A') B = mulVec a b d A B + mulVec a b d A' B := by
  funext M
  simp only [mulVec, Pi.add_apply, add_mul]
  simp_rw [ite_add_zero, Finset.sum_add_distrib]

end Work.HP.Vero
