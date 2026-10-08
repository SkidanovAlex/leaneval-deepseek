import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

/-- If `K` is a subgroup disjoint from the kernel of `f`, then `f` restricts to an
injective map on `K`, hence `K` and its image `K.map f` have the same cardinality. -/
theorem card_map_eq_card_of_disjoint_ker {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup G) (h : Disjoint K f.ker) :
    Nat.card ↥(K.map f) = Nat.card ↥K := by
  have hinj : Function.Injective (fun k : K => f (k : G)) := by
    intro a b hab
    change f (a : G) = f (b : G) at hab
    have hmem : (a : G)⁻¹ * (b : G) ∈ K := K.mul_mem (K.inv_mem a.2) b.2
    have hker : (a : G)⁻¹ * (b : G) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have hbot : (a : G)⁻¹ * (b : G) ∈ (⊥ : Subgroup G) :=
      (disjoint_iff_inf_le.mp h) ⟨hmem, hker⟩
    have h1 : (a : G)⁻¹ * (b : G) = 1 := by rwa [Subgroup.mem_bot] at hbot
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  let g : K → ↑(K.map f) := fun k => ⟨f k, Subgroup.mem_map_of_mem f k.2⟩
  have hbij : Function.Bijective g := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact hinj (congrArg Subtype.val hab)
    · intro y
      obtain ⟨k, hk, hfk⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨k, hk⟩, Subtype.ext hfk⟩
  exact (Nat.card_congr (Equiv.ofBijective g hbij)).symm

end Work.ThreePoints
