import Mathlib.Algebra.Group.Subgroup.Pointwise

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

set_option linter.unusedVariables false

namespace Commons.GroupTheory.Subgroup

theorem centralizer_inf_eq_sup_of_eq_sup_of_le_normalizer_of_central {G : Type*} [Group G]
    (B U T : Subgroup G) (hB : B = U ⊔ T) (hdisj : U ⊓ T = ⊥)
    (hTnorm : T ≤ Subgroup.normalizer (U : Set G))
    {u : G} (hu : u ∈ U) (huc : ∀ a ∈ U, a * u = u * a) :
    Subgroup.centralizer ({u} : Set G) ⊓ B =
      U ⊔ (T ⊓ Subgroup.centralizer ({u} : Set G)) := by
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  -- `U` is contained in the centralizer of `u`
  have hUC : U ≤ C := by
    intro a ha
    rw [hC, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (huc a ha).symm
  apply le_antisymm
  · -- `C ⊓ B ≤ U ⊔ (T ⊓ C)`: write `g = a * t` with `a ∈ U`, `t ∈ T`.
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgC, hgB⟩ := hg
    have hgUT : g ∈ (U ⊔ T : Subgroup G) := hB ▸ hgB
    have hmem : g ∈ (U * T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left U T hTnorm]
      exact hgUT
    obtain ⟨a, ha, t, ht, hat⟩ := Set.mem_mul.mp hmem
    have haC : a ∈ C := hUC ha
    have htC : t ∈ C := by
      have ht_eq : t = a⁻¹ * g := by rw [← hat, inv_mul_cancel_left]
      rw [ht_eq]
      exact C.mul_mem (C.inv_mem haC) hgC
    rw [← hat]
    exact Subgroup.mul_mem_sup ha ⟨ht, htC⟩
  · -- `U ⊔ (T ⊓ C) ≤ C ⊓ B`
    refine le_inf ?_ ?_
    · exact sup_le hUC inf_le_right
    · refine sup_le ?_ ?_
      · rw [hB]; exact le_sup_left
      · rw [hB]; exact inf_le_left.trans le_sup_right

end Commons.GroupTheory.Subgroup