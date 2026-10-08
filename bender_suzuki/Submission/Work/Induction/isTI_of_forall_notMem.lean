import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- The `x ∉ H` form of the TI condition (the form used to define Frobenius complements)
-- implies `Work.Induction.IsTI`: if `x ∉ N_G(H)` then `x ∉ H` because `H ≤ N_G(H)`.
theorem isTI_of_forall_notMem {G : Type*} [Group G] {H : Subgroup G}
    (h : ∀ x : G, x ∉ H → H ⊓ (MulAut.conj x • H) = ⊥) : Work.Induction.IsTI H := by
  intro x hx
  exact h x (fun hxH => hx (Subgroup.le_normalizer hxH))

end Work.Induction
