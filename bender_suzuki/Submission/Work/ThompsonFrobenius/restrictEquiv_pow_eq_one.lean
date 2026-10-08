import Mathlib
import Submission.Work.NPC.Fpf.Defs
import Submission.Work.Frobenius.Fpf.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThompsonFrobenius`: powers of the restriction of an automorphism

M1 of the design note `NOTES_LEAD_bs_thompson.md`: if an automorphism `α` satisfies `α ^ q = 1`,
so does its restriction to an `α`-invariant subgroup.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

open Work.NPC.Fpf

theorem restrictEquiv_pow_eq_one {K : Type*} [Group K] {α : MulAut K} {H : Subgroup K}
    (hH : Work.NPC.Fpf.IsInv α H) {q : ℕ} (hαq : α ^ q = 1) : hH.restrictEquiv ^ q = 1 := by
  refine MulEquiv.ext (fun x => ?_)
  apply Subtype.ext
  rw [IsInv.restrictEquiv_pow_apply, hαq]
  rfl

end Work.ThompsonFrobenius
