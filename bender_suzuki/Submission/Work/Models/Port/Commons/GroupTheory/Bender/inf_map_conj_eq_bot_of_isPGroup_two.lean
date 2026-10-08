import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.existsUnique_fixedPoint_isPGroup_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.GroupTheory.Bender

theorem inf_map_conj_eq_bot_of_isPGroup_two {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω] (heven : Even (Nat.card G)) (hinv : ∀ t : G, orderOf t = 2 → ∃! x : Ω, t • x = x) {S : Subgroup G} (hS : IsPGroup 2 S) {α : Ω} (hα : ∀ s ∈ S, s • α = α) {g : G} (hg : g • α ≠ α) : S ⊓ S.map (MulAut.conj g).toMonoidHom = ⊥ := by
  classical
  let P : Subgroup G := S ⊓ S.map (MulAut.conj g).toMonoidHom
  by_contra hne
  have hPne : P ≠ ⊥ := hne
  have hPS : P ≤ S := inf_le_left
  haveI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  have hP2 : IsPGroup 2 P :=
    hS.of_injective (Subgroup.inclusion hPS) (Subgroup.inclusion_injective hPS)
  obtain ⟨z, hz⟩ := isPGroup_two_exists_center_involution hP2
  let t : G := ((z : P) : G)
  have ht2 : orderOf t = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have ht_mem_S : t ∈ S := (z : P).2.1
  have ht_mem_map : t ∈ S.map (MulAut.conj g).toMonoidHom := (z : P).2.2
  have htα : t • α = α := hα t ht_mem_S
  obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp ht_mem_map
  have htg : t • (g • α) = g • α := by
    rw [← hst, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_smul, mul_smul,
      inv_smul_smul, hα s hs]
  obtain ⟨a, ha, huniq⟩ := hinv t ht2
  have h1 : α = a := huniq α htα
  have h2 : g • α = a := huniq (g • α) htg
  exact hg (h1.trans h2.symm).symm

end Commons.GroupTheory.Bender
