import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ThmF.Setup
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.irrDeg_eq_one_of_commutative

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.Feit`: elementary auxiliary facts

Group-theoretic background for `card_excl` and for the degree computation of the members of
`𝒮 = excludingKernel H Q` in a split rank-one Zassenhaus configuration `IsSplitRankOne H Q t`:

* `(Q.subgroupOf H).Normal` (from `H ≤ N_G(Q)`);
* `Nat.card ↥(Q.subgroupOf H) = Nat.card Q` (and the same for `D = twoPoint H t`);
* the index of `Q` in `H` is `|D|` (from `|H| = |Q|·|D|`);
* `Q` and `D` are complements in `H`;
* the irreducible characters of an abelian `Q` (viewed inside `H`) have degree `1`;
* the unfolding of the definition of `excludingKernel`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausPSL2.Feit

variable {G : Type} [Group G] [Fintype G]
variable {H Q : Subgroup G} {t : G}

/-- `Q ◁ H` in the split rank-one configuration. -/
theorem qSubgroupOf_normal (h : IsSplitRankOne H Q t) : (Q.subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal

/-- `Q`, viewed inside `H`, has the same order as `Q`. -/
theorem card_subgroupOf_Q (h : IsSplitRankOne H Q t) :
    Nat.card ↥(Q.subgroupOf H) = Nat.card Q :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv

/-- `D = twoPoint H t`, viewed inside `H`, has the same order as `D`. -/
theorem card_subgroupOf_D (h : IsSplitRankOne H Q t) :
    Nat.card ↥((twoPoint H t).subgroupOf H) = Nat.card (twoPoint H t) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : twoPoint H t ≤ H)).toEquiv

/-- **The index of `Q` in `H` is `|D|`**, `D = twoPoint H t`: from the two factorisations
`|H| = |Q| · [H : Q]` and `|H| = |Q| · |D|` (`Work.ThmF.split_card_H`). -/
theorem index_subgroupOf_Q (h : IsSplitRankOne H Q t) :
    (Q.subgroupOf H).index = Nat.card (twoPoint H t) := by
  have hcard := Subgroup.card_mul_index (Q.subgroupOf H)
  rw [card_subgroupOf_Q h] at hcard
  have hmul : Nat.card Q * (Q.subgroupOf H).index = Nat.card Q * Nat.card (twoPoint H t) := by
    rw [hcard, Work.ThmF.split_card_H h]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

/-- `Q` and `D = twoPoint H t` are complements in `H`. -/
theorem isComplement'_Q_D (h : IsSplitRankOne H Q t) :
    Subgroup.IsComplement' (Q.subgroupOf H) ((twoPoint H t).subgroupOf H) := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [card_subgroupOf_Q h, card_subgroupOf_D h]
    exact (Work.ThmF.split_card_H h).symm
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxD⟩ := Subgroup.mem_inf.mp hx
    have hxQ' : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hxQ
    have hxD' : (x : G) ∈ twoPoint H t := Subgroup.mem_subgroupOf.mp hxD
    have hbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← h.inf_eq]
      exact ⟨hxQ', hxD'⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hbot))

/-- **Irreducible characters of an abelian `Q`, viewed inside `H`, have degree one.** -/
theorem irrDeg_eq_one_of_mem_Qsub {hab : IsAbelianSubgroup Q} {θ : ↥(Q.subgroupOf H) → ℂ}
    (hθ : θ ∈ Work.CharCore.Irr ↥(Q.subgroupOf H)) : Work.CharCore.irrDeg θ = 1 := by
  haveI : IsMulCommutative ↥(Q.subgroupOf H) :=
    IsMulCommutative.of_comm fun a b => by
      apply Subtype.ext
      apply Subtype.ext
      exact hab (a : G) (Subgroup.mem_subgroupOf.mp a.2) (b : G)
        (Subgroup.mem_subgroupOf.mp b.2)
  exact Work.CharCore.irrDeg_eq_one_of_commutative hθ

/-- Unfolding of `𝒮 = excludingKernel H Q`. -/
theorem mem_excludingKernel_iff {χ : H → ℂ} :
    χ ∈ excludingKernel H Q ↔
      χ ∈ Work.CharCore.Irr H ∧ ∃ x : H, (x : G) ∈ Q ∧ χ x ≠ χ 1 :=
  Finset.mem_filter

end Work.ZassenhausPSL2.Feit
