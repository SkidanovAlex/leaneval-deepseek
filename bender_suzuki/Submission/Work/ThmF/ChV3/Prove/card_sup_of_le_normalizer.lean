import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

/-- If `B` normalizes `A` and `A ⊓ B = ⊥`, then `A ⊔ B` is (as a set) the pointwise
product `A * B`, and the multiplication map `A × B → A ⊔ B` is a bijection; hence the
cardinality of `A ⊔ B` is the product of the cardinalities of `A` and `B`. -/
theorem card_sup_of_le_normalizer {G : Type} [Group G] {A B : Subgroup G}
    (hN : B ≤ Subgroup.normalizer (A : Set G)) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  -- The carrier of `A ⊔ B` is the pointwise product `A * B`.
  have hcoe : (↑(A ⊔ B) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B hN
  -- The multiplication map `A × B → A ⊔ B` is injective, using `A ⊓ B = ⊥`.
  have hinj : Function.Injective
      (fun x : ↥A × ↥B =>
        (⟨x.1.1 * x.2.1, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(A ⊔ B))) := by
    rintro ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩⟩ h
    have h' : a1 * b1 = a2 * b2 := Subtype.ext_iff.mp h
    have h1 : a2⁻¹ * (a1 * b1) = b2 := by rw [h']; group
    have heq : a2⁻¹ * a1 = b2 * b1⁻¹ := by rw [← h1]; group
    have hmemA : a2⁻¹ * a1 ∈ A := A.mul_mem (A.inv_mem ha2) ha1
    have hmemB : a2⁻¹ * a1 ∈ B := by rw [heq]; exact B.mul_mem hb2 (B.inv_mem hb1)
    have hone : a2⁻¹ * a1 = 1 := by
      have hmem : a2⁻¹ * a1 ∈ A ⊓ B := ⟨hmemA, hmemB⟩
      rw [hinf] at hmem
      exact Subgroup.mem_bot.mp hmem
    have haeq : a1 = a2 := (inv_mul_eq_one.mp hone).symm
    have hbeq : b1 = b2 := by rw [haeq] at h'; exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext haeq) (Subtype.ext hbeq)
  -- It is surjective because `↑(A ⊔ B) = ↑A * ↑B`.
  have hsurj : Function.Surjective
      (fun x : ↥A × ↥B =>
        (⟨x.1.1 * x.2.1, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(A ⊔ B))) := by
    intro x
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← hcoe]; exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hbij : Function.Bijective
      (fun x : ↥A × ↥B =>
        (⟨x.1.1 * x.2.1, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(A ⊔ B))) :=
    ⟨hinj, hsurj⟩
  have hcard : Nat.card (↥A × ↥B) = Nat.card ↥(A ⊔ B) :=
    Nat.card_eq_of_bijective _ hbij
  rw [← hcard, Nat.card_prod]

end Work.ThmF.ChV3.Prove
