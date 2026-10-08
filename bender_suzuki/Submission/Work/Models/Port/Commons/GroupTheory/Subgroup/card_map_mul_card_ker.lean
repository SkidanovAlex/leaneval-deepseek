import Mathlib.GroupTheory.Index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

/-- For a group homomorphism with finite (or not) domain, the product of the
cardinalities of the range and kernel equals the cardinality of the domain. -/
lemma card_range_mul_card_ker {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
    Nat.card f.range * Nat.card f.ker = Nat.card G := by
  rw [mul_comm]
  rw [← Subgroup.index_ker (f := f)]
  exact f.ker.card_mul_index

theorem card_map_mul_card_ker {G H : Type*} [Group G] [Group H] [Fintype G]
    (φ : G →* H) (A : Subgroup G) (hker : φ.ker ≤ A) :
    Nat.card (Subgroup.map φ A) * Nat.card (φ.ker : Subgroup G) = Nat.card (A : Subgroup G) := by
  have hformula := card_range_mul_card_ker (f := φ.domRestrict A)
  rw [MonoidHom.domRestrict_range A φ, MonoidHom.ker_domRestrict A φ] at hformula
  have hker_card : Nat.card (φ.ker.subgroupOf A) = Nat.card (φ.ker : Subgroup G) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  rwa [hker_card] at hformula

end Commons.GroupTheory.Subgroup