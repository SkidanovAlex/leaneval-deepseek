import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.RingTheory.Valuation.exists_val_lt_gt_of_independent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation.ValuationSubring

theorem sup_eq_top_approximation {F : Type*} [Field F] (A B : ValuationSubring F)
    (hAB : A ⊔ B = ⊤) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (c₁ c₂ : F) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) :
    ∃ u w : F, A.valuation u < A.valuation c₁ ∧ B.valuation w < B.valuation c₂ ∧ u + w = 1 := by
  rcases le_or_gt (A.valuation c₁) 1 with h1 | h1
  · rcases le_or_gt (B.valuation c₂) 1 with h2 | h2
    · -- main case: `c₁ ∈ A` and `c₂ ∈ B`
      obtain ⟨ρ, hρA, hρB⟩ :=
        Commons.RingTheory.Valuation.exists_val_lt_gt_of_independent A B hAB hA hB
          (A.valuation c₂) ((B.valuation c₁)⁻¹)
          ((Valuation.pos_iff A.valuation).mpr hc₂)
          (inv_pos.mpr ((Valuation.pos_iff B.valuation).mpr hc₁))
      have hc₁pos : 0 < A.valuation c₁ := (Valuation.pos_iff A.valuation).mpr hc₁
      have hc₂pos : 0 < A.valuation c₂ := (Valuation.pos_iff A.valuation).mpr hc₂
      have hc₁Bpos : 0 < B.valuation c₁ := (Valuation.pos_iff B.valuation).mpr hc₁
      have hc₂Bpos : 0 < B.valuation c₂ := (Valuation.pos_iff B.valuation).mpr hc₂
      -- `A`-side: `A.valuation (c₁ * ρ) < A.valuation c₂`
      have hA1 : A.valuation (c₁ * ρ) < A.valuation c₂ := by
        rw [Valuation.map_mul]
        calc A.valuation c₁ * A.valuation ρ ≤ 1 * A.valuation ρ := mul_le_mul_left h1 (A.valuation ρ)
          _ = A.valuation ρ := one_mul _
          _ < A.valuation c₂ := hρA
      have hsumA : A.valuation (c₁ * ρ + c₂) = A.valuation c₂ :=
        Valuation.map_add_eq_of_lt_right A.valuation hA1
      have hne : c₁ * ρ + c₂ ≠ 0 := by
        intro h
        rw [h, Valuation.map_zero] at hsumA
        exact (ne_of_gt hc₂pos) hsumA.symm
      -- `B`-side: `B.valuation (c₁ * ρ) > 1`
      have hB1 : 1 < B.valuation (c₁ * ρ) := by
        rw [Valuation.map_mul]
        calc (1 : B.ValueGroup) = B.valuation c₁ * (B.valuation c₁)⁻¹ :=
              (mul_inv_cancel₀ (ne_of_gt hc₁Bpos)).symm
          _ < B.valuation c₁ * B.valuation ρ := mul_lt_mul_of_pos_left hρB hc₁Bpos
      have hsumB : B.valuation (c₁ * ρ + c₂) = B.valuation (c₁ * ρ) := by
        rw [add_comm]
        exact Valuation.map_add_eq_of_lt_right B.valuation (lt_of_le_of_lt h2 hB1)
      refine ⟨c₁ * ρ / (c₁ * ρ + c₂), c₂ / (c₁ * ρ + c₂), ?_, ?_, ?_⟩
      · rw [Valuation.map_div, hsumA, Valuation.map_mul]
        have h : A.valuation c₁ * A.valuation ρ < A.valuation c₁ * A.valuation c₂ :=
          mul_lt_mul_of_pos_left hρA hc₁pos
        calc A.valuation c₁ * A.valuation ρ / A.valuation c₂
            < A.valuation c₁ * A.valuation c₂ / A.valuation c₂ :=
              (div_lt_div_iff_of_pos_right hc₂pos).mpr h
          _ = A.valuation c₁ := by
              rw [mul_div_assoc, div_self (ne_of_gt hc₂pos), mul_one]
      · rw [Valuation.map_div, hsumB]
        calc B.valuation c₂ / B.valuation (c₁ * ρ)
            = B.valuation c₂ * (B.valuation (c₁ * ρ))⁻¹ := by rw [div_eq_mul_inv]
          _ < B.valuation c₂ * 1 :=
              mul_lt_mul_of_pos_left (inv_lt_one_of_one_lt₀ hB1) hc₂Bpos
          _ = B.valuation c₂ := mul_one _
      · rw [← add_div]
        exact div_self hne
    · -- `c₂ ∉ B`: take `u = 0`, `w = 1`
      refine ⟨0, 1, ?_, ?_, ?_⟩
      · rw [Valuation.map_zero]
        exact (Valuation.pos_iff A.valuation).mpr hc₁
      · rw [Valuation.map_one]; exact h2
      · ring
  · -- `c₁ ∉ A`: take `u = 1`, `w = 0`
    refine ⟨1, 0, ?_, ?_, ?_⟩
    · rw [Valuation.map_one]; exact h1
    · rw [Valuation.map_zero]
      exact (Valuation.pos_iff B.valuation).mpr hc₂
    · ring

end Commons.RingTheory.Valuation.ValuationSubring
