import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Coprime

open scoped Pointwise

/-- The pointwise action of `A` on subgroups commutes with the map to `G` along `N.subtype`:
`(a • S).map N.subtype = a • (S.map N.subtype)` for a subgroup `S ≤ ↥N`. -/
theorem map_subtype_smul_eq_aux {A : Type*} {G : Type*} [Group A] [Group G]
    [MulDistribMulAction A G] (N : Subgroup G) [FT.IsInvariant A N] (a : A)
    (S : Subgroup ↥N) :
    (a • S).map N.subtype = a • (S.map N.subtype) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    exact Subgroup.mem_map.mpr ⟨a⁻¹ • z,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hz, by simp [FT.coe_subgroup_smul]⟩
  · intro hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hy
    refine ⟨a • x, Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr ?_, ?_⟩
    · rw [inv_smul_smul]; exact hx
    · change ((a • x : ↥N) : G) = y
      rw [FT.coe_subgroup_smul]
      change a • N.subtype x = y
      rw [hxeq]
      simp

theorem isInvariant_map_subtype {A : Type*} {G : Type*} [Group A] [Group G] [MulDistribMulAction A G]
    (N : Subgroup G) [FT.IsInvariant A N] (S : Subgroup ↥N) [FT.IsInvariant A S] :
    FT.IsInvariant A (S.map N.subtype) := by
  refine ⟨fun a => ?_⟩
  rw [← map_subtype_smul_eq_aux N a S]
  exact congrArg (fun T : Subgroup ↥N => T.map N.subtype)
    ((inferInstance : FT.IsInvariant A S).smul_eq_self a)

end Work.Coprime
