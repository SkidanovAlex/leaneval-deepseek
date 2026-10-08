import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmG.rankOne_index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `card_G_eq`: the order of a split rank-one group

Feit's count (Peterfalvi II, Ch. VII §1).  In a split rank-one configuration
`H = Q ⋊ D` with `D = twoPoint H t = H ∩ H^t`, the group is the disjoint union of
`H` and the canonical cell `H·t·Q`, so `|G| = |H| + |H|·|Q| = |H|·(|Q| + 1)`, while
`H = Q ⋊ D` gives `|H| = |Q|·|D|`.  Equivalently, `G` acts 2-transitively on
`Ω = G ⧸ H` with point stabiliser `H`, and `Q` is regular on `Ω ∖ {H}`, so
`[G : H] = |Q| + 1`.  Combining: `|G| = (|Q| + 1)·|Q|·|D|`.

The two geometric inputs are already in the library:
* `Work.ThmG.rankOne_index` : `H.index = Nat.card Q + 1`;
* `Work.ThmF.split_card_H`   : `Nat.card H = Nat.card Q * Nat.card (twoPoint H t)`.
-/

set_option autoImplicit false

namespace Work.ZassenhausPSL2.Feit

theorem card_G_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Nat.card G = (Nat.card Q + 1) * Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) := by
  have hindex : H.index = Nat.card Q + 1 := Work.ThmG.rankOne_index h
  have hcardH : Nat.card H = Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) :=
    Work.ThmF.split_card_H h
  have hcard : Nat.card G = H.index * Nat.card H := (Subgroup.index_mul_card H).symm
  rw [hcard, hindex, hcardH]
  ring

end Work.ZassenhausPSL2.Feit
