import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|H| = |Q| · |D|`

`H = Q ⋊ D` with `D = twoPoint H t = H ∩ H^t`: from `Q ⊓ D = ⊥`, `Q ⊔ D = H` and
`D ≤ H ≤ N_G(Q)` (so that Noether's second isomorphism theorem applies in its cardinality
form `|Q ⊔ D| · |Q ⊓ D| = |Q| · |D|`, delivered as
`Work.PGroup.card_sup_mul_card_inf_of_le_normalizer`).
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

theorem card_H_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Nat.card H = Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) := by
  have hnorm : Submission.Blueprint.twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    (inf_le_left : Submission.Blueprint.twoPoint H t ≤ H).trans h.normal
  have hcard := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := Q)
    (K := Submission.Blueprint.twoPoint H t) hnorm
  rw [h.sup_eq, h.inf_eq] at hcard
  simpa using hcard

end Work.ZassenhausTwoGroup
