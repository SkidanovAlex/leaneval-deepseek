import Mathlib
import Submission.Work.ZassenhausSuzuki.QSZPrelim
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.L5Base

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-!
In the Zassenhaus split rank-one setting `H = Q ⋊ D`, `D = twoPoint H t`, with `Q` a Suzuki
two-group, one has `|Q0sub H| = |Z(Q)|` (Suzuki 1962 §8: both equal the number `q` of involutions
of `Q` plus one).

Route: `|Q0sub H| = |Inv(H)| + 1` (`Work.ThmF.L5.card_Q0sub_eq` with `hcomm` from
`Work.ZassenhausSuzuki.invH_commute`); `Inv(H) = Inv(Q)`
(`Work.ZassenhausSuzuki.involutions_H_eq_involutions_Q`); `|Inv(Q)| = |twoPoint H t|`
(`Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions`, with `Q ≠ ⊥` from
`Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split`); and
`|twoPoint H t| + 1 = |Z(Q)|` (`Work.ZassenhausSuzuki.twoPoint_card_add_one_eq_center_card`).
-/

/-- `|Q₀sub H| = |Inv(H)| + 1`, from `Work.ThmF.L5.card_Q0sub_eq`. -/
theorem Q0sub_card_eq_involutions_add_one (h : IsSplitRankOne H Q t) (h2 : IsPGroup 2 Q) :
    Nat.card ↥(Work.ThmF.Q0sub H) = (involutions (H : Set G)).ncard + 1 :=
  Work.ThmF.L5.card_Q0sub_eq (invH_commute h h2)

theorem Q0sub_card_eq_center_card {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q) :
    Nat.card ↥(Work.ThmF.Q0sub H) = Nat.card ↥(Subgroup.center ↥Q) := by
  have hcard : Nat.card ↥(Work.ThmF.Q0sub H) = (involutions (H : Set G)).ncard + 1 :=
    Q0sub_card_eq_involutions_add_one h h2
  have hD : Nat.card ↥(twoPoint H t) = (involutions (Q : Set G)).ncard :=
    Work.ZassenhausPSL2.ZData.card_dStab_eq_card_involutions H Q t h hZ
      (Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split h) h2
  rw [hcard, involutions_H_eq_involutions_Q h h2, ← hD]
  exact twoPoint_card_add_one_eq_center_card h hZ h2 hSuz

end Work.ZassenhausSuzuki
