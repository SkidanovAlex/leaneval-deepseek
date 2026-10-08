import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul
import Submission.Work.ThmG.rankOne_index
import Submission.Work.ZassenhausPSL2.ZData.feit_bound

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `ncard_involutions_G`: the number of involutions in a split rank-one Zassenhaus group

Feit's count (Peterlavi II, Ch. VII §1), leaf `F0b` of the design note
`Submission/Work/ZassenhausPSL2/NOTES_LEAD_bs_psl2core.md`.

For a finite group `G` with a strongly embedded subgroup `H`, split rank-one data `H = Q ⋊ D`
(`D = twoPoint H t = H ⊓ Hᵗ`) and a Zassenhaus action on `G ⧸ H`:

  `#Inv(G) = (|Q| + 1) · |D|`.

Assembly:
* `Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul` counts the involutions of
  a finite group relative to a strongly embedded subgroup: `#Inv(G) = [G : H] · #Inv(H)`;
* `Work.ThmG.rankOne_index` gives `[G : H] = |Q| + 1`;
* `Work.ZassenhausPSL2.ZData.ncard_involutions_Q_eq_card_twoPoint` gives
  `#Inv(Q) = |D|`, and `ncard_involutions_Q_eq` says the involutions of `Q` are those of `H`.

Note that neither simplicity of `G`, nor commutativity of `Q`, nor that `Q` is a `2`-group is
needed: the three inputs above hold under the stated hypotheses alone (this covers both the
`PSL(2, 2ⁿ)` case, where `Q` is elementary abelian of order `q`, and the Suzuki case, where `Q`
is a non-abelian Suzuki `2`-group of order `q²`).
-/

set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2.Feit

/-- The involutions of a subgroup `K ≤ G`, viewed as a subset of `G`, correspond to the
involutions of the group `K`: `orderOf` is the same in `K` and in `G`. -/
lemma ncard_involutions_subgroup {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    (Submission.Blueprint.involutions (K : Set G)).ncard =
      Nat.card {u : ↥K // orderOf u = 2} := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
      invFun := fun u => ⟨(u.1 : G), ⟨u.1.2, ?_⟩⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun u => Subtype.ext (Subtype.ext rfl) }
  · rw [← Subgroup.orderOf_coe]
    exact x.2.2
  · rw [Subgroup.orderOf_coe]
    exact u.2

theorem ncard_involutions_G {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) :
    ({g : G | orderOf g = 2} : Set G).ncard =
      (Nat.card Q + 1) * Nat.card (Submission.Blueprint.twoPoint H t) := by
  classical
  -- the involutions of `H` are the involutions of `Q`, and there are `|D|` of them
  have hInvH : Nat.card {u : ↥H // orderOf u = 2} =
      Nat.card (Submission.Blueprint.twoPoint H t) := by
    rw [← ncard_involutions_subgroup H]
    exact (Work.ZassenhausPSL2.ZData.ncard_involutions_Q_eq h hz).symm.trans
      (Work.ZassenhausPSL2.ZData.ncard_involutions_Q_eq_card_twoPoint h hz)
  -- counting involutions relative to the strongly embedded subgroup `H`
  have hmain : Nat.card {g : G // orderOf g = 2} =
      (Nat.card Q + 1) * Nat.card (Submission.Blueprint.twoPoint H t) := by
    rw [Commons.GroupTheory.StronglyEmbedded.card_involutions_eq_index_mul H
      h.stronglyEmbedded.1 h.stronglyEmbedded.2.1 h.stronglyEmbedded.2.2,
      Work.ThmG.rankOne_index h, hInvH]
  rw [← Nat.card_coe_set_eq]
  exact hmain

end Work.ZassenhausPSL2.Feit
