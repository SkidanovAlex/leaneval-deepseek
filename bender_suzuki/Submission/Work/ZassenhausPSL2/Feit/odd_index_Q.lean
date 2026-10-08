import Mathlib
import Submission.Work.ZassenhausPSL2.Feit.card_G_eq
import Submission.Work.ZassenhausPSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `odd_index_Q`: `Q` has odd index in `G`

In a split rank-one configuration `H = Q ⋊ D` (`D = twoPoint H t = H ∩ Hᵗ`) with `H`
strongly embedded, `|G : Q|` is odd, i.e. `Q` contains a Sylow `2`-subgroup of `G`.

The count is purely arithmetic:
* `|H| = |Q| · |D|` (`Work.ThmF.split_card_H`);
* `D` has odd order (strong embeddedness, `t ∉ H`);
* `H` has even order (strong embeddedness), so `|Q|` is even;
* `|G : H| = |Q| + 1` (`Work.ThmG.rankOne_index`), and `|G| = |G : H| · |H|`, hence
  `|G : Q| = (|Q| + 1) · |D|`, a product of an odd and an even number.

The hypothesis `IsPGroup 2 Q` is not needed for this count (the evenness of `|Q|` already
follows from strong embeddedness); it is kept as it appears in the caller's statement.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausPSL2.Feit

theorem odd_index_Q {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (h2 : IsPGroup 2 Q) : Odd Q.index := by
  have hcardH : Nat.card H = Nat.card Q * Nat.card (Submission.Blueprint.twoPoint H t) :=
    Work.ThmF.split_card_H h
  have hevenH : Even (Nat.card H) := Work.ThmF.split_even_card_H h
  have hoddD : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
    Work.ThmF.split_odd_card_twoPoint h
  -- `|Q|` is even: `|H| = |Q| · |D|` is even while `|D|` is odd
  have hevenQ : Even (Nat.card Q) := by
    rcases Nat.even_mul.mp (hcardH ▸ hevenH) with hQ | hD
    · exact hQ
    · exact absurd hD (Nat.not_even_iff_odd.mpr hoddD)
  have hoddQ1 : Odd (Nat.card Q + 1) :=
    Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr hevenQ)
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  -- `|G : Q| = |G : H| · |H : Q| = (|Q| + 1) · |D|`
  have hindex : Q.index = (Nat.card Q + 1) * Nat.card (Submission.Blueprint.twoPoint H t) := by
    refine Nat.eq_of_mul_eq_mul_right hQpos ?_
    rw [Subgroup.index_mul_card Q, card_G_eq h]
    ring
  rw [hindex]
  exact Odd.mul hoddQ1 hoddD

end Work.ZassenhausPSL2.Feit
