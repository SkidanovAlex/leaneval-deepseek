import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.IntermediateField

lemma add_mul_sub_mul_eq {K E : Type*} [Field K] [Field E] [Algebra K E]
    {π : K} {α : E} (hα : α ^ 2 = algebraMap K E π) (a b : K) :
    (algebraMap K E a + algebraMap K E b * α) * (algebraMap K E a - algebraMap K E b * α)
      = algebraMap K E (a ^ 2 - b ^ 2 * π) := by
  have h1 : (algebraMap K E a + algebraMap K E b * α) * (algebraMap K E a - algebraMap K E b * α)
      = (algebraMap K E a) ^ 2 - (algebraMap K E b) ^ 2 * α ^ 2 := by ring
  rw [h1, hα, map_sub, map_mul, map_pow, map_pow]

theorem mem_adjoin_sq_eq {K E : Type*} [Field K] [Field E] [Algebra K E]
    {π : K} {α : E} (hα : α ^ 2 = algebraMap K E π)
    (hαK : α ∉ Set.range (algebraMap K E)) :
    ∀ x : E, x ∈ IntermediateField.adjoin K {α} ↔
      ∃ a b : K, x = algebraMap K E a + algebraMap K E b * α := by
  intro x
  constructor
  · intro hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨0, 1, by simp⟩
    | algebraMap c => exact ⟨c, 0, by simp⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨a₁, b₁, rfl⟩ := ihx
        obtain ⟨a₂, b₂, rfl⟩ := ihy
        refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
        rw [map_add, map_add]
        ring
    | mul x y hx hy ihx ihy =>
        obtain ⟨a₁, b₁, rfl⟩ := ihx
        obtain ⟨a₂, b₂, rfl⟩ := ihy
        refine ⟨a₁ * a₂ + b₁ * b₂ * π, a₁ * b₂ + b₁ * a₂, ?_⟩
        have h1 : (algebraMap K E a₁ + algebraMap K E b₁ * α) *
              (algebraMap K E a₂ + algebraMap K E b₂ * α)
            = algebraMap K E a₁ * algebraMap K E a₂
              + algebraMap K E b₁ * algebraMap K E b₂ * α ^ 2
              + (algebraMap K E a₁ * algebraMap K E b₂ + algebraMap K E b₁ * algebraMap K E a₂) * α := by
          ring
        rw [h1, hα]
        simp only [map_add, map_mul]
    | inv x hx ihx =>
        obtain ⟨a, b, rfl⟩ := ihx
        by_cases hc : a ^ 2 - b ^ 2 * π = 0
        · have hzero : (algebraMap K E a + algebraMap K E b * α) *
              (algebraMap K E a - algebraMap K E b * α) = 0 := by
            rw [add_mul_sub_mul_eq hα a b, hc, map_zero]
          rcases mul_eq_zero.mp hzero with h | h
          · rw [h, inv_zero]
            exact ⟨0, 0, by simp⟩
          · have hx0 : algebraMap K E a + algebraMap K E b * α = 0 := by
              have hb0 : b = 0 := by
                by_contra hb
                apply hαK
                have hbne : algebraMap K E b ≠ 0 := fun h0 =>
                  hb ((algebraMap K E).injective (by rw [h0, map_zero]))
                have hA : algebraMap K E a = algebraMap K E b * α := by
                  rw [sub_eq_zero] at h
                  exact h
                refine ⟨b⁻¹ * a, ?_⟩
                rw [map_mul, map_inv₀, hA, ← mul_assoc, inv_mul_cancel₀ hbne, one_mul]
              rw [hb0] at h ⊢
              simpa using h
            rw [hx0, inv_zero]
            exact ⟨0, 0, by simp⟩
        · have hcne : algebraMap K E (a ^ 2 - b ^ 2 * π) ≠ 0 := fun h0 =>
            hc ((algebraMap K E).injective (by rw [h0, map_zero]))
          have hmul : (algebraMap K E a + algebraMap K E b * α) *
              ((algebraMap K E a - algebraMap K E b * α)
                * (algebraMap K E (a ^ 2 - b ^ 2 * π))⁻¹) = 1 := by
            rw [← mul_assoc, add_mul_sub_mul_eq hα a b, mul_inv_cancel₀ hcne]
          have hxinv : (algebraMap K E a + algebraMap K E b * α)⁻¹
              = (algebraMap K E a - algebraMap K E b * α)
                * (algebraMap K E (a ^ 2 - b ^ 2 * π))⁻¹ :=
            inv_eq_of_mul_eq_one_right hmul
          rw [hxinv]
          refine ⟨(a ^ 2 - b ^ 2 * π)⁻¹ * a, -((a ^ 2 - b ^ 2 * π)⁻¹ * b), ?_⟩
          simp only [map_mul, map_inv₀, map_neg]
          ring
  · rintro ⟨a, b, rfl⟩
    exact add_mem (IntermediateField.algebraMap_mem _ a)
      (mul_mem (IntermediateField.algebraMap_mem _ b)
        (IntermediateField.subset_adjoin K {α} (Set.mem_singleton α)))

end Commons.FieldTheory.IntermediateField