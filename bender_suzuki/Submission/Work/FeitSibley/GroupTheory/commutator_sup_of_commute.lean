import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.GroupTheory

open scoped Pointwise commutatorElement

/-- If two subgroups commute elementwise, then every element of their join is a product of an
element of the first and an element of the second. -/
private theorem exists_mem_mul_of_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hle : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer (B : Set G) (by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (h a ha b hb).symm)
  have hset : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp (hset ▸ hx')
  exact ⟨a, ha, b, hb, hab⟩

/-- **The derived subgroup of the join of two elementwise commuting subgroups.**
If `A` and `B` commute elementwise then `⁅A ⊔ B, A ⊔ B⁆ = ⁅A, A⁆ ⊔ ⁅B, B⁆`. -/
theorem commutator_sup_of_commute {G : Type*} [Group G] (A B : Subgroup G)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ⁅A ⊔ B, A ⊔ B⁆ = ⁅A, A⁆ ⊔ ⁅B, B⁆ := by
  refine le_antisymm ?_ (sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
    (Subgroup.commutator_mono le_sup_right le_sup_right))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mem_mul_of_mem_sup_of_commute h hx
  obtain ⟨c, hc, d, hd, rfl⟩ := exists_mem_mul_of_mem_sup_of_commute h hy
  have hbc : ⁅b, c⁆ = 1 := Commute.commutator_eq (h c hc b hb).symm
  have had : ⁅a, d⁆ = 1 := Commute.commutator_eq (h a ha d hd)
  have hac : (a * c) * ⁅b, d⁆ * (a * c)⁻¹ = ⁅b, d⁆ := by
    have h1 : a * ⁅b, d⁆ * a⁻¹ = ⁅b, d⁆ := by
      rw [conjugate_commutatorElement, h a ha b hb, h a ha d hd]
      simp [mul_assoc]
    have h2 : c * ⁅b, d⁆ * c⁻¹ = ⁅b, d⁆ := by
      rw [conjugate_commutatorElement, h c hc b hb, h c hc d hd]
      simp [mul_assoc]
    calc (a * c) * ⁅b, d⁆ * (a * c)⁻¹ = a * (c * ⁅b, d⁆ * c⁻¹) * a⁻¹ := by group
      _ = a * ⁅b, d⁆ * a⁻¹ := by rw [h2]
      _ = ⁅b, d⁆ := h1
  have hexp : ⁅a * b, c * d⁆ = (a * c) * ⁅b, d⁆ * (a * c)⁻¹ * ⁅a, c⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_mul_right_eq_mul_conj, hbc, had]
    group
  rw [hexp, hac]
  exact ((⁅A, A⁆ : Subgroup G) ⊔ ⁅B, B⁆).mul_mem
    (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hb hd))
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha hc))

end Work.FeitSibley.GroupTheory
