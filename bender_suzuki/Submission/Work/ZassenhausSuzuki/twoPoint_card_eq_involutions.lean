import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions
import Submission.Work.ZassenhausPSL2.Feit.qomegaData_nonempty

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `D = H ∩ H^t` is regular on the involutions of `Q`

The cardinality form of "the two-point stabiliser permutes the involutions of the root group
regularly" (Suzuki Prop. 3; Peterfalvi II Ch. V §1): `|D| = #Inv(Q)`.

This is the first half of L2 (`twoPoint_cyclic`) of the lead's design note
`NOTES_LEAD_probe1630.md`; it is routed through the delivered
`Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions`, with `Q ≠ ⊥` supplied by
`Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split` (so no extra hypothesis is needed).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem twoPoint_card_eq_involutions {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (h2 : IsPGroup 2 Q) :
    Nat.card ↥(twoPoint H t) = (involutions (Q : Set G)).ncard :=
  Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions H Q t h hZ
    (Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split h) h2

end Work.ZassenhausSuzuki
