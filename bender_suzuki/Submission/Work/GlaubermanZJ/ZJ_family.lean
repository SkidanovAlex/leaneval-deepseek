import Mathlib
import Submission.Work.GlaubermanZJ.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The family defining `J(P)` in the blueprint's `thompsonJ`

`Submission.Blueprint.thompsonJ P` is the supremum of the abelian subgroups of `P` "of maximal
order", i.e. of the subgroups `A ≤ P` that are abelian and dominate every abelian `B ≤ P` in
`Nat.card`:
```
Submission.Blueprint.thompsonJ P =
  ⨆ (A : Subgroup G) (_ : A ≤ P ∧ IsAbelianSubgroup A ∧
        ∀ B : Subgroup G, B ≤ P → IsAbelianSubgroup B → Nat.card B ≤ Nat.card A), A.
```
This file names that family (`ZJfam`) so that the invariance of `J(P)` under `N_G(P)` — and hence
the lemma `Work.GlaubermanZJ.normalizer_ZJ` — can be stated as a clean statement about `ZJfam`.

`ZJfam` is a copy of the predicate appearing in `Submission.Blueprint.thompsonJ`, so
`thompsonJ_eq_iSup_ZJfam` is definitional.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GlaubermanZJ

variable {G : Type*} [Group G]

/-- The family of subgroups whose supremum is the blueprint's Thompson subgroup `J(P)`: the
abelian subgroups `A ≤ P` of maximal order.  The condition is written exactly as in
`Submission.Blueprint.thompsonJ`, so that `ZJfam P A` is *definitionally* the predicate there. -/
def ZJfam (P A : Subgroup G) : Prop :=
  A ≤ P ∧ Submission.Blueprint.IsAbelianSubgroup A ∧
    ∀ B : Subgroup G, B ≤ P → Submission.Blueprint.IsAbelianSubgroup B → Nat.card B ≤ Nat.card A

/-- The blueprint's `thompsonJ` is the supremum over `ZJfam P` (definitional). -/
theorem thompsonJ_eq_iSup_ZJfam (P : Subgroup G) :
    Submission.Blueprint.thompsonJ P = ⨆ (A : Subgroup G) (_ : ZJfam P A), A := rfl

end Work.GlaubermanZJ
