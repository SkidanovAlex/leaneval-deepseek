import Mathlib

namespace Work.CORE4.A4bAux

theorem card_map_quot {H : Type*} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    {A : Subgroup H} (h : A ⊓ Z = ⊥) :
    Nat.card ↥(A.map (QuotientGroup.mk' Z)) = Nat.card ↥A := by
  -- `h : A ⊓ Z = ⊥` says `A` and `Z` are disjoint, hence `Z.subgroupOf A = ⊥`.
  have hdisj : Disjoint Z A := by rw [disjoint_iff, inf_comm]; exact h
  have hsub : Z.subgroupOf A = ⊥ := Subgroup.subgroupOf_eq_bot.mpr hdisj
  -- `Subgroup.relIndex_ker` computes the cardinality of the image as a relative index,
  -- and `(mk' Z).ker = Z`; then `Z.subgroupOf A = ⊥` has full index in `A`.
  rw [← Subgroup.relIndex_ker A (QuotientGroup.mk' Z), QuotientGroup.ker_mk',
    Subgroup.relIndex, hsub, Subgroup.index_bot]

end Work.CORE4.A4bAux
