import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.MulDefs

/-! `mulVec` is linear in its first argument (scalars). -/
set_option autoImplicit false
noncomputable section
open Finset
namespace Work.HP.Vero

theorem mulVec_smul_left {a b d n : ℕ} {R : Type*} [CommSemiring R]
    (c : R) (A : Mon a n → R) (B : Mon b n → R) :
    mulVec a b d (c • A) B = c • mulVec a b d A B := by
  funext M
  simp only [mulVec, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  split <;> simp [mul_assoc]

end Work.HP.Vero
