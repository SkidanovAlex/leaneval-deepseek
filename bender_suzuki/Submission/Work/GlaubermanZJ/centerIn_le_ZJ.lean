import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.PGroup.centerIn_le_ZJ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Z(P) ≤ Z(J(P))` in the blueprint's vocabulary

The blueprint's `Submission.Blueprint.ZJ P = J(P) ⊓ C_G(J(P))` and the delivered
`Work.PGroup.ZJ P = Z(J(P))` (`Work.PGroup.centerIn` applied to the delivered Thompson subgroup)
are the same subgroup — this is `Work.GlaubermanZJ.ZJ_eq`, which combines
`Work.GlaubermanZJ.thompsonJ_eq` with the elementary identification
`H ⊓ C_G(H) = Z(H)`.

It therefore remains to know the classical fact `Z(P) ≤ Z(J(P))` for a finite subgroup `P`:
every `z ∈ Z(P)` centralises `P`, hence `J(P) ≤ P`; and `z` lies in `J(P)` because adjoining `z`
to an abelian subgroup of `P` of maximal order produces another abelian subgroup of `P` of
maximal order.  That is exactly `Work.PGroup.centerIn_le_ZJ`.
-/

set_option autoImplicit false

namespace Work.GlaubermanZJ

/-- The centre of a finite subgroup `P` is contained in `Z(J(P))`, in the blueprint's
formulation `Submission.Blueprint.ZJ = J(P) ⊓ C_G(J(P))`. -/
theorem centerIn_le_ZJ {G : Type*} [Group G] (P : Subgroup G) [Finite P] :
    Work.PGroup.centerIn P ≤ Submission.Blueprint.ZJ P := by
  rw [ZJ_eq P]
  exact Work.PGroup.centerIn_le_ZJ P

end Work.GlaubermanZJ
