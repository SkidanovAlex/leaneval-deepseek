import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.even_card_Q`

In the split rank-one set-up `IsSplitRankOne H Q t` the subgroup `Q` has even order.

Only the strongly embedded hypothesis on `H` and the decomposition `H = Q ⋊ D` with
`D = H ∩ Hᵗ` (`IsSplitRankOne.inf_eq`, `IsSplitRankOne.sup_eq`) are used:

* `|D|` is odd (`IsStronglyEmbedded` applied to `t ∉ H`) while `|H|` is even;
* `Q` and `D` are complementary subgroups of `H` (`Q ⊓ D = ⊥`, `Q ⊔ D = H` with `Q ◁ H`),
  hence `|H| = |Q| · |D|`;
* an even number which is the product of `|Q|` and an odd number forces `|Q|` even.

The Zassenhaus hypothesis is not needed for this statement.
-/

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Pointwise

namespace Work.ZassenhausTwoGroup

/-- In a split rank-one configuration `Q` and `D = H ∩ Hᵗ` are complementary subgroups of `H`,
so `|H| = |Q| * |D|`. -/
theorem card_eq_mul_card_twoPoint {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) : Nat.card H = Nat.card Q * Nat.card (twoPoint H t) := by
  have hDle : twoPoint H t ≤ H := inf_le_left
  have hsup : Q.subgroupOf H ⊔ (twoPoint H t).subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.le hDle, h.sup_eq, Subgroup.subgroupOf_self]
  have hinf : Q.subgroupOf H ⊓ (twoPoint H t).subgroupOf H = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    have hx' : (x : G) ∈ Q ⊓ twoPoint H t := ⟨hx.1, hx.2⟩
    rw [h.inf_eq, Subgroup.mem_bot] at hx'
    exact Subtype.ext (by simpa using hx')
  have hnorm : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  have hmul : (↑(Q.subgroupOf H) : Set H) * (↑((twoPoint H t).subgroupOf H) : Set H) =
      Set.univ := by
    rw [← @Subgroup.normal_mul H _ (Q.subgroupOf H) ((twoPoint H t).subgroupOf H) hnorm,
      hsup, Subgroup.coe_top]
  have hdisj : Disjoint (Q.subgroupOf H) ((twoPoint H t).subgroupOf H) := disjoint_iff.mpr hinf
  have hcard := (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul).card_mul_card
  have hcard' : Nat.card Q * Nat.card (twoPoint H t) = Nat.card H := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv] at hcard
  exact hcard'.symm

theorem even_card_Q {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Even (Nat.card Q) := by
  have hEvenH : Even (Nat.card H) := h.stronglyEmbedded.2.1
  have hOddD : Odd (Nat.card (twoPoint H t)) := h.stronglyEmbedded.2.2 t h.not_mem
  have hcard : Nat.card H = Nat.card Q * Nat.card (twoPoint H t) :=
    card_eq_mul_card_twoPoint h
  by_contra hQ
  have hOddQ : Odd (Nat.card Q) := Nat.not_even_iff_odd.mp hQ
  have hOddH : Odd (Nat.card H) := hcard ▸ hOddQ.mul hOddD
  exact absurd hOddH (Nat.not_odd_iff_even.mpr hEvenH)

end Work.ZassenhausTwoGroup
