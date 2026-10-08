import Mathlib

namespace Work.A7REC.Char

theorem card_mul_card_le_card_of_inf_eq_bot {G : Type*} [Group G] {A B K : Subgroup G} [Finite ↥K]
    (hA : A ≤ K) (hB : B ≤ K) (h : A ⊓ B = ⊥) :
    Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥K := by
  -- The multiplication map `A × B → K` is injective when `A ⊓ B = ⊥`.
  rw [← Nat.card_prod]
  apply Nat.card_le_card_of_injective (β := ↥K)
    (fun p : ↥A × ↥B => (⟨(p.1 : G) * (p.2 : G), mul_mem (hA p.1.2) (hB p.2.2)⟩ : ↥K))
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ heq
  simp only [Subtype.mk.injEq] at heq
  -- `a * b = a' * b'` gives `a'⁻¹ * a = b' * b⁻¹`, which lies in `A ⊓ B = ⊥`.
  have key : a'⁻¹ * a = b' * b⁻¹ := by
    have := congrArg (fun t => a'⁻¹ * t * b⁻¹) heq
    simpa [mul_assoc] using this
  have hxA : a'⁻¹ * a ∈ A := mul_mem (inv_mem ha') ha
  have hxB : a'⁻¹ * a ∈ B := by rw [key]; exact mul_mem hb' (inv_mem hb)
  have hxbot : a'⁻¹ * a ∈ (⊥ : Subgroup G) := by
    rw [← h]; exact Subgroup.mem_inf.mpr ⟨hxA, hxB⟩
  have ha_eq : a = a' := (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hxbot)).symm
  have hyB : b' * b⁻¹ ∈ B := mul_mem hb' (inv_mem hb)
  have hyA : b' * b⁻¹ ∈ A := by rw [← key]; exact hxA
  have hybot : b' * b⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← h]; exact Subgroup.mem_inf.mpr ⟨hyA, hyB⟩
  have hb_eq : b' = b := mul_inv_eq_one.mp (Subgroup.mem_bot.mp hybot)
  exact Prod.ext (Subtype.ext ha_eq) (Subtype.ext hb_eq.symm)

end Work.A7REC.Char
