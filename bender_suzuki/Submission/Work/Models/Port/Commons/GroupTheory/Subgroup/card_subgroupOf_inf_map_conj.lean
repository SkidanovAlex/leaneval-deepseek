import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.SetTheory.Cardinal.Finite

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem card_subgroupOf_inf_map_conj {G : Type*} [Group G] (H K : Subgroup G) (h : H ≤ K) (g : ↥K) :
    Nat.card ↥(H.subgroupOf K ⊓ (H.subgroupOf K).map (MulAut.conj g).toMonoidHom) =
    Nat.card ↥(H ⊓ H.map (MulAut.conj (g : G)).toMonoidHom) := by
  -- Coercion identity between conjugation inside the subgroup `K` and in `G`.
  have hkey : ∀ y : ↥K,
      (((MulAut.conj g).toMonoidHom) y : G) = ((MulAut.conj (g : G)).toMonoidHom) (y : G) := by
    intro y
    rfl
  -- The image of `H.subgroupOf K` under conjugation by `g ∈ K`, as a subgroup of `K`,
  -- equals the subgroup of `K` consisting of the elements of `H.map (conj g)`.
  have hmap : (H.subgroupOf K).map (MulAut.conj g).toMonoidHom
      = (H.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf K := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨(y : G), hy, ?_⟩
      rw [← hkey y, hyx]
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨y, h hy⟩, hy, ?_⟩
      apply Subtype.ext
      rw [hkey ⟨y, h hy⟩]
      simpa using hyx
  have heq : (H ⊓ H.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf K
      = H.subgroupOf K ⊓ (H.subgroupOf K).map (MulAut.conj g).toMonoidHom := by
    have h1 : (H ⊓ H.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf K
        = H.subgroupOf K ⊓ (H.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf K := by
      simp only [Subgroup.subgroupOf, Subgroup.comap_inf]
    rw [h1, hmap]
  rw [← heq]
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (le_trans inf_le_left h)).toEquiv

end Commons.GroupTheory.Subgroup