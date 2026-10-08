import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Commutator

theorem commutator_le_sup_commutator_of_sup_eq_top {G : Type*} [Group G] (N H : Subgroup G) [N.Normal] (h : N ⊔ H = ⊤) : commutator G ≤ N ⊔ ⁅H, H⁆ := by
  -- Work in the quotient `G ⧸ N`, where the image of `H` is everything.
  have hmapN : Subgroup.map (QuotientGroup.mk' N) N = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hmapH : Subgroup.map (QuotientGroup.mk' N) H = ⊤ := by
    have h1 : Subgroup.map (QuotientGroup.mk' N) (N ⊔ H) = Subgroup.map (QuotientGroup.mk' N) H := by
      rw [Subgroup.map_sup N H (QuotientGroup.mk' N), hmapN, bot_sup_eq]
    rw [← h1, h]
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
  -- In the quotient the commutator subgroup of the image of `H` is the whole commutator.
  have heq : Subgroup.map (QuotientGroup.mk' N) (commutator G) =
      Subgroup.map (QuotientGroup.mk' N) ⁅H, H⁆ := by
    have htop : Subgroup.map (QuotientGroup.mk' N) (⊤ : Subgroup G) = ⊤ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
    rw [show commutator G = ⁅(⊤ : Subgroup G), ⊤⁆ from rfl,
      Subgroup.map_commutator, Subgroup.map_commutator, htop, hmapH]
  have hle : Subgroup.map (QuotientGroup.mk' N) (commutator G) ≤
      Subgroup.map (QuotientGroup.mk' N) ⁅H, H⁆ := le_of_eq heq
  rw [Subgroup.map_le_map_iff, QuotientGroup.ker_mk', sup_comm] at hle
  exact hle

end Commons.GroupTheory.Commutator