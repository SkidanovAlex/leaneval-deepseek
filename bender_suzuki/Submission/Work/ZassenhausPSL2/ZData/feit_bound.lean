import Submission.Work.ZassenhausPSL2.ZData.FeitBoundAux
import Submission.Work.ZassenhausPSL2.Feit.card_excl
import Submission.Work.ZassenhausPSL2.FeitCln.card_excl_eq_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.ZData.feit_bound` — Z1 of the lead's design

Feit's inequality for the split rank-one (Zassenhaus) data `(H, Q, t)` with `Q` an abelian
`2`-group, i.e. Feit 1960, eq. (28) specialised to abelian `Q`.

The auxiliary development (`isolation of the statement`, `|𝒟| ∣ |Q| - 1`, `|𝒟| = |Inv(Q)|`,
`arith_card_eq`, and the equivalence with `Q` being elementary abelian) lives in
`Submission.Work.ZassenhausPSL2.ZData.FeitBoundAux`, so that the files of the leaf decomposition
F0–F8 in `Submission/Work/ZassenhausPSL2/Feit/` (which import this module for those auxiliary
lemmas) do not create an import cycle with the leaves used here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

namespace Work.ZassenhausPSL2.ZData

theorem feit_bound {G : Type} [Group G] [Finite G] (H Q : Subgroup G) (t : G)
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q)
    (hsimple : IsSimpleGroup G) :
    2 * Nat.card (Submission.Blueprint.twoPoint H t) + 1 ≥ Nat.card Q := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : IsSimpleGroup G := hsimple
  -- F2b: `|𝒮| · |D| = |Q| - 1`
  have hcard : (Submission.Blueprint.excludingKernel H Q).card *
      Nat.card (Submission.Blueprint.twoPoint H t) = Nat.card Q - 1 :=
    Work.ZassenhausPSL2.Feit.card_excl h hz h2 hab
  -- F8: `|𝒮| = 1`
  have hone : (Submission.Blueprint.excludingKernel H Q).card = 1 :=
    Work.ZassenhausPSL2.FeitCln.card_excl_eq_one h hz h2 hab
  have hQ1 : Nat.card Q - 1 = Nat.card (Submission.Blueprint.twoPoint H t) := by
    rw [← hcard, hone, one_mul]
  exact arith_bound_of_card_eq _ _ Nat.card_pos hQ1

end Work.ZassenhausPSL2.ZData
