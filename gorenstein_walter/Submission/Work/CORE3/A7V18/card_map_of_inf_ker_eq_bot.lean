import Mathlib

namespace Work.CORE3.A7V18

/-- If a subgroup `K` meets the kernel of `f` trivially, then `f` restricts to a
bijection `K ≃ K.map f`, so the two subgroups have the same cardinality. -/
theorem card_map_of_inf_ker_eq_bot {G H : Type*} [Group G] [Group H]
    (f : G →* H) (K : Subgroup G) (h : K ⊓ f.ker = ⊥) : Nat.card (K.map f) = Nat.card K := by
  -- `f` is injective on `K`
  have key : ∀ x y : K, f (x : G) = f (y : G) → x = y := by
    intro x y hxy
    have hmul : (x : G) * (y : G)⁻¹ ∈ K ⊓ f.ker := by
      refine ⟨K.mul_mem x.2 (K.inv_mem y.2), ?_⟩
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    rw [h] at hmul
    have hx : (x : G) * (y : G)⁻¹ = 1 := Subgroup.mem_bot.mp hmul
    exact Subtype.ext (mul_inv_eq_one.mp hx)
  -- hence the restriction is a bijection onto the image
  refine (Nat.card_congr ?_).symm
  refine Equiv.ofBijective
    (fun x : K => (⟨f (x : G), Subgroup.mem_map.mpr ⟨(x : G), x.2, rfl⟩⟩ : K.map f)) ⟨?_, ?_⟩
  · intro x y hxy
    exact key x y (Subtype.ext_iff.mp hxy)
  · intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hxK, hfx⟩
    exact ⟨⟨x, hxK⟩, Subtype.ext hfx⟩

end Work.CORE3.A7V18
