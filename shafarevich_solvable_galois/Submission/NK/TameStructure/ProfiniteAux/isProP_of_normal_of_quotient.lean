/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# An extension of a pro-`p` group by a pro-`p` group is pro-`p`

`NK.LocalTame.IsProP p` is the finite-quotient formulation of "pro-`p`".  This file records
that the class is closed under extensions: if `N ⊴ G` is pro-`p` and `G ⧸ N` is pro-`p` then `G`
is pro-`p`.  The proof is the classical index computation

  `[G : M] = [G : M ⊔ N] · [M ⊔ N : M] = [G ⧸ N : (M ⊔ N) ⧸ N] · [N : M ⊓ N]`.
-/
import Mathlib
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalTame.ProP.isProP_iSup_of_normal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructure.ProfiniteAux

open NK.LocalTame

/-- **The comap of the image of a subgroup containing the kernel.**  For a surjective `f` and
`N ≤ G` with `f.ker ≤ N`, the preimage of the image of `N` is `N`. -/
theorem comap_map_eq_self_of_le_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {N : Subgroup G} (hN : f.ker ≤ N) : (N.map f).comap f = N := by
  refine le_antisymm ?_ (Subgroup.le_comap_map f N)
  intro x hx
  rw [Subgroup.mem_comap, Subgroup.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have h1 : y⁻¹ * x ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have h2 : y⁻¹ * x ∈ N := hN h1
  have : x = y * (y⁻¹ * x) := by group
  rw [this]
  exact N.mul_mem hy h2

/-- **An extension of pro-`p` groups is pro-`p`**: if `N ⊴ G` and both `N` and `G ⧸ N` are
pro-`p` in the sense of `NK.LocalTame.IsProP p` (every normal subgroup of finite index has
`p`-power index), then so is `G`. -/
theorem isProP_of_normal_of_quotient {G : Type*} [Group G] {p : ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsProP p ↥N) (hQ : IsProP p (G ⧸ N)) : IsProP p G := by
  intro M hMnorm hMfin
  haveI := hMnorm
  have hker : (QuotientGroup.mk' N).ker ≤ M ⊔ N := by
    rw [QuotientGroup.ker_mk']
    exact le_sup_right
  haveI hsup : (M ⊔ N).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  haveI hmap : ((M ⊔ N).map (QuotientGroup.mk' N)).FiniteIndex :=
    ⟨by
      rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N),
        comap_map_eq_self_of_le_ker _ (QuotientGroup.mk'_surjective N) hker]
      exact hsup.index_ne_zero⟩
  obtain ⟨i, hi⟩ := hQ ((M ⊔ N).map (QuotientGroup.mk' N)) hmap
  obtain ⟨j, hj⟩ := hN (M.subgroupOf N) inferInstance
  refine ⟨i + j, ?_⟩
  have hsub : (M.subgroupOf N).index = (M.subgroupOf (M ⊔ N)).index :=
    NK.LocalTame.ProP.index_subgroupOf_eq_of_normal hMnorm
  have hQindex : (M ⊔ N).index = ((M ⊔ N).map (QuotientGroup.mk' N)).index := by
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N),
      comap_map_eq_self_of_le_ker _ (QuotientGroup.mk'_surjective N) hker]
  calc M.index = M.relIndex (M ⊔ N) * (M ⊔ N).index :=
        (Subgroup.relIndex_mul_index le_sup_left).symm
    _ = (M.subgroupOf N).index * (M ⊔ N).index := by
        rw [show M.relIndex (M ⊔ N) = (M.subgroupOf (M ⊔ N)).index from rfl, ← hsub]
    _ = (M.subgroupOf N).index * ((M ⊔ N).map (QuotientGroup.mk' N)).index := by rw [hQindex]
    _ = p ^ j * p ^ i := by rw [hj, hi]
    _ = p ^ (i + j) := by rw [← pow_add, Nat.add_comm]

end NK.TameStructure.ProfiniteAux
