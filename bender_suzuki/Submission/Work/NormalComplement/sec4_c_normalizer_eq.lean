import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.NormalComplement

/-- Auxiliary: `A ⊔ P` is the pointwise product `A * P` when `P` lies in the normalizer of `A`.
This is the decomposition used to write every element of `V = A ⊔ P` as a product. -/
private lemma sec4_c_coe_sup_eq_mul {G : Type*} [Group G] (A P : Subgroup G)
    (h : P ≤ Subgroup.normalizer (A : Set G)) :
    ((A ⊔ P : Subgroup G) : Set G) = (A : Set G) * (P : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left A P h

theorem sec4_c_normalizer_eq {G : Type*} [Group G] {D V A P : Subgroup G}
    (hVD : V ≤ D) (hA : A ≤ V) (hAnorm : V ≤ Subgroup.normalizer (A : Set G))
    (hAP : A ⊓ P = ⊥) (hAsup : A ⊔ P = V) (hPle : P ≤ V)
    (hNV : D ⊓ Subgroup.normalizer (P : Set G) ≤ V) :
    D ⊓ Subgroup.normalizer (P : Set G) =
      (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P := by
  -- Key step: `A ⊓ N_G(P) = A ⊓ C_G(P)`.  Since `A` is normalised by `V = A ⊔ P`
  -- and `A ⊓ P = ⊥`, any `x ∈ A` normalising `P` must centralise it.
  have hkey : A ⊓ Subgroup.normalizer (P : Set G) = A ⊓ Subgroup.centralizer (P : Set G) := by
    apply le_antisymm
    · rintro x ⟨hxA, hxN⟩
      refine Subgroup.mem_inf.mpr ⟨hxA, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hzP : x * p * x⁻¹ * p⁻¹ ∈ P :=
        P.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN p).mp hp) (P.inv_mem hp)
      have hzA : x * p * x⁻¹ * p⁻¹ ∈ A := by
        have hpN : p ∈ Subgroup.normalizer (A : Set G) := hAnorm (hPle hp)
        have h2 : p * x⁻¹ * p⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp hpN x⁻¹).mp (A.inv_mem hxA)
        rw [show x * p * x⁻¹ * p⁻¹ = x * (p * x⁻¹ * p⁻¹) by group]
        exact A.mul_mem hxA h2
      have hzbot : x * p * x⁻¹ * p⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hAP]
        exact Subgroup.mem_inf.mpr ⟨hzA, hzP⟩
      have hz1 : x * p * x⁻¹ * p⁻¹ = 1 := Subgroup.mem_bot.mp hzbot
      have hxp : x * p * x⁻¹ = p := mul_inv_eq_one.mp hz1
      calc p * x = (x * p * x⁻¹) * x := by rw [hxp]
        _ = x * p := by group
    · rintro x ⟨hxA, hxC⟩
      exact Subgroup.mem_inf.mpr
        ⟨hxA, Subgroup.centralizer_le_normalizer (P : Set G) hxC⟩
  apply le_antisymm
  · -- Forward inclusion, via the decomposition `V = A * P`.
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (P : Set G) := hx.2
    have hxV : x ∈ V := hNV hx
    have hprod : ((A ⊔ P : Subgroup G) : Set G) = (A : Set G) * (P : Set G) :=
      sec4_c_coe_sup_eq_mul A P (hPle.trans hAnorm)
    have hxAP : x ∈ (A : Set G) * (P : Set G) := by rw [← hprod, hAsup]; exact hxV
    obtain ⟨a, haA, p, hpP, hap⟩ := Set.mem_mul.mp hxAP
    have haN : a ∈ Subgroup.normalizer (P : Set G) := by
      have hap' : a = x * p⁻¹ := by rw [← hap]; group
      rw [hap']
      exact (Subgroup.normalizer (P : Set G)).mul_mem hxN
        ((Subgroup.normalizer (P : Set G)).inv_mem (Subgroup.le_normalizer hpP))
    have hmem : a ∈ A ⊓ Subgroup.centralizer (P : Set G) := by
      rw [← hkey]
      exact Subgroup.mem_inf.mpr ⟨haA, haN⟩
    rw [← hap]
    exact Subgroup.mul_mem_sup hmem hpP
  · -- Reverse inclusion.
    apply sup_le
    · exact le_inf (le_trans inf_le_left (hA.trans hVD))
        (le_trans inf_le_right (Subgroup.centralizer_le_normalizer (P : Set G)))
    · exact le_inf (hPle.trans hVD) Subgroup.le_normalizer

end Work.NormalComplement
