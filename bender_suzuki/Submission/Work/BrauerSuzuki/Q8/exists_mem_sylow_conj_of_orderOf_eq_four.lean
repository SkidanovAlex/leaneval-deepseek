import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

open scoped Pointwise

/-- Every element of order `4` of a finite group is conjugate to an element of order `4`
lying in any prescribed Sylow `2`-subgroup.

Indeed, `⟨y⟩` is a `2`-subgroup, hence lies in some Sylow `2`-subgroup `P`; since Sylow
`2`-subgroups are conjugate, `P` is a conjugate of `S`, and conjugating `y` into `S`
preserves its order and its conjugacy class. -/
theorem exists_mem_sylow_conj_of_orderOf_eq_four {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {y : G} (hy : orderOf y = 4) :
    ∃ x : G, x ∈ (S : Subgroup G) ∧ orderOf x = 4 ∧ IsConj y x := by
  have hP : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_zpowers, hy]
    norm_num
  obtain ⟨P, hPy⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) (α := Sylow 2 G) P S
  refine ⟨g * y * g⁻¹, ?_, ?_, ?_⟩
  · have hyP : y ∈ (P : Subgroup G) := hPy (Subgroup.mem_zpowers y)
    have hS : (S : Subgroup G) = MulAut.conj g • (P : Subgroup G) := by
      rw [show (S : Subgroup G) = ((g • P : Sylow 2 G) : Subgroup G) from by rw [hg],
          Sylow.coe_subgroup_smul]
    have hmem : MulAut.conj g • y ∈ (S : Subgroup G) := by
      rw [hS]
      exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (P : Subgroup G) hyP
    simpa [MulAut.conj_apply] using hmem
  · have hsem : SemiconjBy g y (g * y * g⁻¹) := by
      unfold SemiconjBy; group
    rw [← SemiconjBy.orderOf_eq g hsem, hy]
  · rw [isConj_iff]; exact ⟨g, rfl⟩

end Work.BrauerSuzuki.Q8
