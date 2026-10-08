import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement

namespace Commons.GroupTheory.Commutator

theorem commutator_le_of_eq_sup_of_le_normalizer_of_commutator_le {G : Type*} [Group G]
    (U T B : Subgroup G) (hB : B = U ⊔ T) (hU : B ≤ Subgroup.normalizer (U : Set G))
    (hTT : ⁅T, T⁆ ≤ U) : ⁅B, B⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  have hTU : T ≤ Subgroup.normalizer (U : Set G) :=
    fun t ht => hU (by rw [hB]; exact Subgroup.mem_sup_right ht)
  have hset : (↑(U ⊔ T) : Set G) = (U : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left U T hTU
  have hdecomp : ∀ b ∈ B, ∃ u ∈ U, ∃ t ∈ T, u * t = b := by
    intro b hb
    have hb' : b ∈ (↑(U ⊔ T) : Set G) := by
      rw [← hB]
      exact hb
    rw [hset] at hb'
    exact Set.mem_mul.mp hb'
  intro b1 hb1 b2 hb2
  obtain ⟨u1, hu1, t1, ht1, rfl⟩ := hdecomp b1 hb1
  obtain ⟨u2, hu2, t2, ht2, rfl⟩ := hdecomp b2 hb2
  have ht1B : t1 ∈ B := by rw [hB]; exact Subgroup.mem_sup_right ht1
  have ht2B : t2 ∈ B := by rw [hB]; exact Subgroup.mem_sup_right ht2
  have hconj : ∀ (b : G), b ∈ B → ∀ u ∈ U, b * u * b⁻¹ ∈ U :=
    fun b hb u hu => (Subgroup.le_normalizer_iff.mp hU) b hb u hu
  have hcomm : ⁅t1, t2⁆ ∈ U := hTT (Subgroup.commutator_mem_commutator ht1 ht2)
  rw [commutatorElement_def]
  have key : u1 * t1 * (u2 * t2) * (u1 * t1)⁻¹ * (u2 * t2)⁻¹
      = u1 * (t1 * u2 * t1⁻¹) * ⁅t1, t2⁆ * (t2 * u1⁻¹ * t2⁻¹) * u2⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [key]
  exact U.mul_mem (U.mul_mem (U.mul_mem (U.mul_mem hu1 (hconj t1 ht1B u2 hu2)) hcomm)
    (hconj t2 ht2B u1⁻¹ (U.inv_mem hu1))) (U.inv_mem hu2)

end Commons.GroupTheory.Commutator