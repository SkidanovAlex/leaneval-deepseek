import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.PSU3.StageA

/-- Intersecting with `L` commutes with the pointwise infimum of subgroups:
`(A ⊓ B).subgroupOf L = A.subgroupOf L ⊓ B.subgroupOf L`. -/
theorem subgroupOf_inf {G : Type*} [Group G] (A B L : Subgroup G) :
    (A ⊓ B).subgroupOf L = A.subgroupOf L ⊓ B.subgroupOf L := by
  ext x; simp [Subgroup.mem_inf, Subgroup.mem_subgroupOf]

theorem conj_subgroupOf_inf {G : Type*} [Group G] {L A : Subgroup G} (hAL : A ≤ L) (g : L) :
    (A.subgroupOf L) ⊓ ((A.subgroupOf L).map (MulAut.conj g).toMonoidHom)
      = (A ⊓ A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf L := by
  -- The pointwise action of `MulAut` on `Subgroup` agrees with `Subgroup.map`.
  have h1 : (A.subgroupOf L).map (MulAut.conj g).toMonoidHom = MulAut.conj g • (A.subgroupOf L) := by
    rw [Subgroup.pointwise_smul_def]; congr 1
  have h2 : A.map (MulAut.conj (g : G)).toMonoidHom = MulAut.conj (g : G) • A := by
    rw [Subgroup.pointwise_smul_def]; congr 1
  -- Conjugation commutes with `subgroupOf`.
  have h3 := Subgroup.conj_smul_subgroupOf hAL g
  rw [h1, h3, h2, subgroupOf_inf]

end Work.PSU3.StageA
