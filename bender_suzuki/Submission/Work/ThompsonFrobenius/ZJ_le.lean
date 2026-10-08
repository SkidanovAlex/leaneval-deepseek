import Mathlib
import Submission.Work.ThompsonFrobenius.BlueprintZJ
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Z(J(P)) ≤ P` (area `ThompsonFrobenius`)

`Submission.Blueprint.ZJ P = J(P) ⊓ C_G(J(P))`, so every element of `Z(J(P))` lies in `J(P)`,
and `J(P)` is by construction the supremum of the subgroups `A ≤ P` that are abelian of maximal
order inside `P`:

`Submission.Blueprint.thompsonJ P = ⨆ (A : Subgroup G) (_ : A ≤ P ∧ …), A`.

A supremum of subgroups all contained in `P` is contained in `P`, so `thompsonJ P ≤ P` and hence
`ZJ P ≤ thompsonJ P ≤ P`.  This is proved here directly from the definition; the statement is
also available (for the `GlaubermanZJ` area) as `Work.GlaubermanZJ.ZJ_le`.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

/-- Thompson's subgroup `J(P)` is contained in `P`: it is the supremum of the subgroups `A ≤ P`
that are abelian of maximal order in `P`, and a supremum of subgroups contained in `P` is itself
contained in `P`. -/
theorem thompsonJ_le {G : Type*} [Group G] (P : Subgroup G) :
    Submission.Blueprint.thompsonJ P ≤ P := by
  unfold Submission.Blueprint.thompsonJ
  exact iSup_le fun A => iSup_le fun hA => hA.1

/-- `Z(J(P)) ≤ P`: `Z(J(P)) ≤ J(P) ≤ P`. -/
theorem ZJ_le {G : Type*} [Group G] (P : Subgroup G) : Submission.Blueprint.ZJ P ≤ P := by
  rw [Submission.Blueprint.ZJ]
  exact le_trans inf_le_left (thompsonJ_le P)

end Work.ThompsonFrobenius
