import Mathlib
import Submission.Work.NPC.All
import Submission.Work.NPC.Frobenius.hasNormalPComplement_of_normal_pGroup_quotient
import Submission.Work.Frobenius.Fpf.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# M2: the normal `p`-complement is invariant under every automorphism (area `ThompsonFrobenius`)

A normal `p`-complement is unique (`Work.NPC.Basic.isNormalPComplement_unique`) and is carried to a
normal `p`-complement by every automorphism
(`Work.NPC.Frobenius.isNormalPComplement_map_mulEquiv`), hence is fixed by every automorphism, i.e.
invariant (`Work.Frobenius.Fpf.isInv_of_map_eq`).
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem isInv_of_isNormalPComplement {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (α : MulAut K) {N : Subgroup K} (hN : Work.NPC.IsNormalPComplement p N) :
    Work.NPC.Fpf.IsInv α N :=
  Work.Frobenius.Fpf.isInv_of_map_eq
    (Work.NPC.Basic.isNormalPComplement_unique
      (Work.NPC.Frobenius.isNormalPComplement_map_mulEquiv hN α) hN)

end Work.ThompsonFrobenius
