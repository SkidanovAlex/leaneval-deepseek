import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

/-- Membership form of `Subgroup.normalizer_subgroupOf`: an element `n` of `N` normalizes the
subgroup `P.subgroupOf N` of `↥N` (where `P ≤ N`) if and only if, viewed in `G`, it normalizes
`P`. -/
lemma mem_normalizer_subgroupOf_iff {G : Type*} [Group G] (P N : Subgroup G) (hPN : P ≤ N)
    (n : ↥N) :
    n ∈ Subgroup.normalizer ((P.subgroupOf N : Subgroup ↥N) : Set ↥N)
      ↔ (n : G) ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff, Subgroup.mem_set_normalizer_iff]
  constructor
  · intro hn h
    constructor
    · intro hP
      have hN : h ∈ N := hPN hP
      have key := hn ⟨h, hN⟩
      have h1 : (⟨h, hN⟩ : ↥N) ∈ (P.subgroupOf N) := (Subgroup.mem_subgroupOf).mpr hP
      have h2 : n * ⟨h, hN⟩ * n⁻¹ ∈ (P.subgroupOf N) := key.mp h1
      have h3 := (Subgroup.mem_subgroupOf).mp h2
      simpa using h3
    · intro hP
      have hN2 : (n : G) * h * (n : G)⁻¹ ∈ N := hPN hP
      have hnN : (n : G) ∈ N := n.2
      have hGN : h ∈ N := by
        have : h = (n : G)⁻¹ * ((n : G) * h * (n : G)⁻¹) * (n : G) := by group
        rw [this]
        exact N.mul_mem (N.mul_mem (N.inv_mem hnN) hN2) hnN
      have key := hn ⟨h, hGN⟩
      have h1 : n * ⟨h, hGN⟩ * n⁻¹ ∈ (P.subgroupOf N) := (Subgroup.mem_subgroupOf).mpr hP
      have h2 : (⟨h, hGN⟩ : ↥N) ∈ (P.subgroupOf N) := key.mpr h1
      have h3 := (Subgroup.mem_subgroupOf).mp h2
      simpa using h3
  · intro hn h
    have key := hn (h : G)
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    simpa using key

/-- The normalizer, inside `N`, of the subgroup `P.subgroupOf N` of `↥N` (where `P ≤ N`) coincides
with `N_G(P) ∩ N` viewed as a subgroup of `↥N`. -/
theorem normalizer_subgroupOf {G : Type*} [Group G] (P N : Subgroup G) (hPN : P ≤ N) :
    Subgroup.normalizer ((P.subgroupOf N : Subgroup ↥N) : Set ↥N)
      = (Subgroup.normalizer (P : Set G) ⊓ N).subgroupOf N := by
  ext n
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [mem_normalizer_subgroupOf_iff P N hPN n]
  exact ⟨fun h => ⟨h, n.2⟩, fun h => h.1⟩

end Commons.GroupTheory.Subgroup