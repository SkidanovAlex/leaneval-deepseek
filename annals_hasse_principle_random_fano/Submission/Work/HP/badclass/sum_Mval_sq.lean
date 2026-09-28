import Mathlib
import Submission.Work.HP.badclass.BadDefs

set_option autoImplicit false
noncomputable section

open MvPolynomial Finset

namespace Work.HP.badclass

/-- Double counting: the second moment of `Mval` is the sum over pairs of the intersections. -/
theorem sum_Mval_sq (d n p : ℕ) [NeZero p] :
    (∑ a : Work.HP.Mon d n → ZMod p, Work.HP.Mval d n p a ^ 2)
      = ∑ x ∈ Work.HP.torFinset n p, ∑ y ∈ Work.HP.torFinset n p,
          ((Work.HP.Dset d n p x) ∩ (Work.HP.Dset d n p y)).ncard := by
  classical
  have key : ∀ a : Work.HP.Mon d n → ZMod p, Work.HP.Mval d n p a ^ 2 =
      ∑ x ∈ Work.HP.torFinset n p, ∑ y ∈ Work.HP.torFinset n p,
        (if a ∈ Work.HP.Dset d n p x then 1 else 0) *
          (if a ∈ Work.HP.Dset d n p y then 1 else 0) := by
    intro a
    rw [sq, Work.HP.Mval, Finset.sum_mul_sum]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Work.HP.ncard_eq_filter_card, Finset.card_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h1 : a ∈ Work.HP.Dset d n p x <;>
    by_cases h2 : a ∈ Work.HP.Dset d n p y <;> simp [h1, h2]

end Work.HP.badclass
