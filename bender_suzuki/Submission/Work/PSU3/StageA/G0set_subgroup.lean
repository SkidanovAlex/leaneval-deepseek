import Mathlib
import Submission.Work.PSU3.StageA.G0Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.PSU3.StageA

theorem G0set_subgroup {G : Type} [Group G] {H Q K : Subgroup G} {t : G}
    (ht2 : t * t = 1) (hKH : K ≤ H)
    (hQH : H ≤ Subgroup.normalizer (Q : Set G))
    (hKinv : ∀ k ∈ K, t * k * t = k⁻¹)
    (hQt : ∀ x ∈ Q, t * x * t ∈ Work.PSU3.StageA.G0set Q K t) :
    ∃ S : Subgroup G, (S : Set G) = Work.PSU3.StageA.G0set Q K t := by
  classical
  -- `K` normalises `Q` (as `K ≤ H ≤ N(Q)`), so `P := Q ⊔ K = Q · K`.
  have hKN : K ≤ Subgroup.normalizer (Q : Set G) := hKH.trans hQH
  set P : Subgroup G := Q ⊔ K with hPdef
  have hPK : ((P : Set G)) = (Q : Set G) * (K : Set G) := by
    rw [hPdef]; exact Subgroup.coe_mul_of_right_le_normalizer_left Q K hKN
  have memP : ∀ x : G, x ∈ (P : Set G) ↔ ∃ q ∈ Q, ∃ k ∈ K, q * k = x := by
    intro x
    rw [hPK, Set.mem_mul]
    exact ⟨fun h => h, fun h => h⟩
  -- the second piece `A = P · t · Q` of `G₀ = P ∪ A`
  set A : Set G := {x : G | ∃ p : G, p ∈ (P : Set G) ∧ ∃ q : G, q ∈ Q ∧ x = p * t * q}
    with hAdef
  have memA : ∀ x : G, x ∈ A ↔ ∃ p ∈ (P : Set G), ∃ q ∈ Q, x = p * t * q := fun x => Iff.rfl
  have hG0A : Work.PSU3.StageA.G0set Q K t = (P : Set G) ∪ A := by
    rw [hAdef, hPdef]; rfl
  have hQt' : ∀ x ∈ Q, t * x * t ∈ (P : Set G) ∪ A := by
    intro x hx; rw [← hG0A]; exact hQt x hx
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hKinv' : ∀ k ∈ K, t * k⁻¹ * t = k := by
    intro k hk
    have h := hKinv k⁻¹ (K.inv_mem hk)
    rwa [inv_inv] at h
  have hKtinv : ∀ k ∈ K, t * k⁻¹ = k * t := by
    intro k hk
    calc t * k⁻¹ = t * k⁻¹ * (t * t) := by rw [ht2, mul_one]
      _ = (t * k⁻¹ * t) * t := by group
      _ = k * t := by rw [hKinv' k hk]
  -- `A · t · Q ⊆ P ∪ A`
  have hAtQ : ∀ a ∈ A, ∀ q ∈ Q, a * t * q ∈ (P : Set G) ∪ A := by
    intro a ha q hq
    obtain ⟨p, hp, q₀, hq₀, rfl⟩ := (memA a).mp ha
    rw [show p * t * q₀ * t * q = p * (t * q₀ * t) * q from by group]
    rcases hQt' q₀ hq₀ with hv | hv
    · exact Or.inl (P.mul_mem (P.mul_mem hp hv) (Subgroup.mem_sup_left hq))
    · obtain ⟨p₁, hp₁, q₁, hq₁, hv_eq⟩ := (memA _).mp hv
      rw [hv_eq, show p * (p₁ * t * q₁) * q = (p * p₁) * t * (q₁ * q) from by group]
      exact Or.inr ((memA _).mpr ⟨p * p₁, P.mul_mem hp hp₁, q₁ * q, Q.mul_mem hq₁ hq, rfl⟩)
  -- `P · t · P ⊆ P ∪ A`
  have hPtP : ∀ p ∈ (P : Set G), ∀ y ∈ (P : Set G), p * t * y ∈ (P : Set G) ∪ A := by
    intro p hp y hy
    obtain ⟨q₁, hq₁, k₁, hk₁, h₁⟩ := (memP p).mp hp
    obtain ⟨q₂, hq₂, k₂, hk₂, h₂⟩ := (memP y).mp hy
    have hk₂inv : k₂⁻¹ ∈ K := K.inv_mem hk₂
    rw [← h₁, ← h₂]
    rcases hQt' q₂ hq₂ with hu | hu
    · -- `t q₂ t ∈ P`
      refine Or.inr ((memA _).mpr ⟨q₁ * k₁ * (t*q₂*t) * k₂⁻¹, ?_, 1, Q.one_mem, ?_⟩)
      · exact P.mul_mem (P.mul_mem (P.mul_mem (Subgroup.mem_sup_left hq₁) (Subgroup.mem_sup_right hk₁)) hu) (Subgroup.mem_sup_right hk₂inv)
      · rw [mul_one]
        rw [show q₁ * k₁ * (t*q₂*t) * k₂⁻¹ * t = q₁ * k₁ * t * q₂ * (t * k₂⁻¹ * t) from by group, hKinv' k₂ hk₂]
        group
    · -- `t q₂ t ∈ A`
      obtain ⟨p₀, hp₀, q₀, hq₀, hu_eq⟩ := (memA _).mp hu
      have hnorm : k₂ ∈ Subgroup.normalizer (Q : Set G) := hKN hk₂
      have hkq : k₂ * q₀ * k₂⁻¹ ∈ Q := by
        simpa using (Subgroup.mem_normalizer_iff.mp hnorm q₀).mp hq₀
      have hstep1 : q₁ * k₁ * t * (q₂ * k₂) = q₁ * k₁ * (t * q₂ * t) * k₂⁻¹ * t := by
        rw [show q₁ * k₁ * (t * q₂ * t) * k₂⁻¹ * t = q₁ * k₁ * t * q₂ * (t * k₂⁻¹ * t) from by group,
            hKinv' k₂ hk₂]
        group
      have hE : q₁ * k₁ * t * (q₂ * k₂) = q₁ * k₁ * p₀ * k₂ * (t * (k₂ * q₀ * k₂⁻¹) * t) := by
        rw [hstep1, hu_eq]
        rw [show q₁ * k₁ * (p₀ * t * q₀) * k₂⁻¹ * t = q₁ * k₁ * p₀ * t * (q₀ * k₂⁻¹) * t from by group]
        rw [show q₀ * k₂⁻¹ = k₂⁻¹ * (k₂ * q₀ * k₂⁻¹) from by group]
        rw [show q₁ * k₁ * p₀ * t * (k₂⁻¹ * (k₂ * q₀ * k₂⁻¹)) * t = q₁ * k₁ * p₀ * (t * k₂⁻¹) * (k₂ * q₀ * k₂⁻¹) * t from by group]
        rw [hKtinv k₂ hk₂]
        group
      rcases hQt' (k₂ * q₀ * k₂⁻¹) hkq with hv | hv
      · refine Or.inl ?_
        rw [hE]
        exact P.mul_mem (P.mul_mem (P.mul_mem (P.mul_mem (Subgroup.mem_sup_left hq₁) (Subgroup.mem_sup_right hk₁)) hp₀) (Subgroup.mem_sup_right hk₂)) hv
      · obtain ⟨p', hp', q', hq', hv_eq⟩ := (memA _).mp hv
        refine Or.inr ?_
        rw [hE, hv_eq]
        exact (memA _).mpr ⟨q₁ * k₁ * p₀ * k₂ * p', P.mul_mem (P.mul_mem (P.mul_mem (P.mul_mem (Subgroup.mem_sup_left hq₁) (Subgroup.mem_sup_right hk₁)) hp₀) (Subgroup.mem_sup_right hk₂)) hp', q', hq', by group⟩
  -- `P · A ⊆ A`
  have hPA : ∀ p ∈ (P : Set G), ∀ a ∈ A, p * a ∈ A := by
    intro p hp a ha
    obtain ⟨p₁, hp₁, q, hq, rfl⟩ := (memA a).mp ha
    exact (memA _).mpr ⟨p * p₁, P.mul_mem hp hp₁, q, hq, by group⟩
  -- `A · P ⊆ P ∪ A`
  have hAP : ∀ a ∈ A, ∀ p ∈ (P : Set G), a * p ∈ (P : Set G) ∪ A := by
    intro a ha p hp
    obtain ⟨p₀, hp₀, q, hq, rfl⟩ := (memA a).mp ha
    rw [show p₀ * t * q * p = p₀ * t * (q * p) from by group]
    exact hPtP p₀ hp₀ (q * p) (P.mul_mem (Subgroup.mem_sup_left hq) hp)
  -- `A · A ⊆ P ∪ A`
  have hAA : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ (P : Set G) ∪ A := by
    intro a ha b hb
    obtain ⟨p, hp, q, hq, rfl⟩ := (memA a).mp ha
    obtain ⟨p', hp', q', hq', rfl⟩ := (memA b).mp hb
    rw [show p * t * q * (p' * t * q') = (p * t * (q * p')) * t * q' from by group]
    rcases hPtP p hp (q * p') (P.mul_mem (Subgroup.mem_sup_left hq) hp') with hw | hw
    · exact Or.inr ((memA _).mpr ⟨p * t * (q * p'), hw, q', hq', rfl⟩)
    · exact hAtQ (p * t * (q * p')) hw q' hq'
  -- `A⁻¹ ⊆ A`
  have hAinv : ∀ a ∈ A, a⁻¹ ∈ A := by
    intro a ha
    obtain ⟨p, hp, q, hq, rfl⟩ := (memA a).mp ha
    obtain ⟨q₁, hq₁, k₁, hk₁, h₁⟩ := (memP p).mp hp
    have hk1inv : k₁⁻¹ ∈ K := K.inv_mem hk₁
    have hnorm : k₁⁻¹ ∈ Subgroup.normalizer (Q : Set G) := hKN hk1inv
    have hqQ : k₁⁻¹ * q⁻¹ * k₁ ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp hnorm q⁻¹).mp (Q.inv_mem hq)
    refine (memA _).mpr ⟨k₁ * (k₁⁻¹ * q⁻¹ * k₁), ?_, q₁⁻¹, Q.inv_mem hq₁, ?_⟩
    · exact P.mul_mem (Subgroup.mem_sup_right hk₁) (Subgroup.mem_sup_left hqQ)
    · rw [← h₁]
      calc (q₁ * k₁ * t * q)⁻¹ = q⁻¹ * t * k₁⁻¹ * q₁⁻¹ := by
              rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hti]; group
        _ = q⁻¹ * (t * k₁⁻¹) * q₁⁻¹ := by group
        _ = q⁻¹ * (k₁ * t) * q₁⁻¹ := by rw [hKtinv k₁ hk₁]
        _ = (k₁ * (k₁⁻¹ * q⁻¹ * k₁)) * t * q₁⁻¹ := by group
  refine ⟨{ carrier := (P : Set G) ∪ A
            one_mem' := Or.inl P.one_mem
            mul_mem' := ?_
            inv_mem' := ?_ }, ?_⟩
  · intro a b ha hb
    rw [Set.mem_union] at ha hb ⊢
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (P.mul_mem ha hb)
    · exact Or.inr (hPA a ha b hb)
    · exact hAP a ha b hb
    · exact hAA a ha b hb
  · intro a ha
    rw [Set.mem_union] at ha ⊢
    rcases ha with ha | ha
    · exact Or.inl (P.inv_mem ha)
    · exact Or.inr (hAinv a ha)
  · exact hG0A.symm

end Work.PSU3.StageA
