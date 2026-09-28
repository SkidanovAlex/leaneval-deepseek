import Mathlib
import Submission.Work.HP.badclass.BadDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
noncomputable section

open MvPolynomial Finset

namespace Work.HP.badclass

/-- Double counting: the first moment of `Mval` is the sum of the sizes of the `Dset x`. -/
theorem sum_Mval (d n p : ℕ) [NeZero p] :
    (∑ a : Work.HP.Mon d n → ZMod p, Work.HP.Mval d n p a)
      = ∑ x ∈ Work.HP.torFinset n p, (Work.HP.Dset d n p x).ncard := by
  classical
  have key : ∀ a : Work.HP.Mon d n → ZMod p,
      Work.HP.Mval d n p a
        = ∑ x ∈ Work.HP.torFinset n p, if a ∈ Work.HP.Dset d n p x then 1 else 0 := by
    intro a
    rw [Work.HP.Mval]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Work.HP.ncard_eq_filter_card, Finset.card_filter]

end Work.HP.badclass
