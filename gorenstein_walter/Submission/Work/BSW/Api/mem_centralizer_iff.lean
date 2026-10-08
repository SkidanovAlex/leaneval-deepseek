import Mathlib
import Submission.Work.BSW.Basic

namespace Work.BSW.Api

/-- Normal form for `H = C_G(t) = K⟨s⟩`: an element of `H` lies in `K` or is `k * s` with
`k ∈ K`. -/
theorem mem_centralizer_iff {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (x : G) :
    x ∈ Subgroup.centralizer ({t} : Set G) ↔ x ∈ K ∨ ∃ k ∈ K, x = k * s := by
  have hct := Work.BSW.centralizer_t_eq h
  have hinv := Work.BSW.inverts_s_K h
  have hs2 := Work.BSW.s_mul_self h
  have hsinv := Work.BSW.s_inv h
  -- `s` conjugates an element of `K` to its inverse, so it can be pushed to the right.
  have hsconj : ∀ b ∈ K, s * b = b⁻¹ * s := by
    intro b hb
    have hb' := hinv b hb
    calc s * b = (s * b * s⁻¹) * s := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = b⁻¹ * s := by rw [hb']
  have hsconj' : ∀ b ∈ K, s * b⁻¹ = b * s := by
    intro b hb
    have hb' := hinv b⁻¹ (K.inv_mem hb)
    simp only [inv_inv] at hb'
    calc s * b⁻¹ = (s * b⁻¹ * s⁻¹) * s := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = b * s := by rw [hb']
  -- The set `K ∪ K s` is a subgroup: this is what makes the normal form `K ⊔ ⟨s⟩ = K ∪ K s`.
  let T : Subgroup G :=
    { carrier := {x | x ∈ K ∨ ∃ k ∈ K, x = k * s}
      one_mem' := Or.inl K.one_mem
      mul_mem' := by
        intro a b ha hb
        rcases ha with ha | ⟨ka, hka, rfl⟩
        · rcases hb with hb | ⟨kb, hkb, rfl⟩
          · exact Or.inl (K.mul_mem ha hb)
          · exact Or.inr ⟨a * kb, K.mul_mem ha hkb, by rw [mul_assoc]⟩
        · rcases hb with hb | ⟨kb, hkb, rfl⟩
          · refine Or.inr ⟨ka * b⁻¹, K.mul_mem hka (K.inv_mem hb), ?_⟩
            rw [mul_assoc, hsconj b hb, ← mul_assoc]
          · refine Or.inl ?_
            have hval : ka * s * (kb * s) = ka * kb⁻¹ := by
              calc ka * s * (kb * s) = ka * (s * kb) * s := by noncomm_ring
                _ = ka * (kb⁻¹ * s) * s := by rw [hsconj kb hkb]
                _ = ka * kb⁻¹ * (s * s) := by noncomm_ring
                _ = ka * kb⁻¹ := by rw [hs2, mul_one]
            rw [hval]
            exact K.mul_mem hka (K.inv_mem hkb)
      inv_mem' := by
        intro a ha
        rcases ha with ha | ⟨ka, hka, rfl⟩
        · exact Or.inl (K.inv_mem ha)
        · exact Or.inr ⟨ka, hka, by rw [mul_inv_rev, hsinv, hsconj' ka hka]⟩ }
  have hKle : K ≤ T := fun a ha => Or.inl ha
  have hzp : Subgroup.zpowers s ≤ T :=
    Subgroup.zpowers_le.mpr (Or.inr ⟨1, K.one_mem, (one_mul s).symm⟩)
  constructor
  · intro hx
    have hx' : x ∈ K ⊔ Subgroup.zpowers s := by rw [← hct]; exact hx
    exact sup_le hKle hzp hx'
  · intro hx
    rw [hct]
    rcases hx with hx | ⟨k, hk, rfl⟩
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))

end Work.BSW.Api
