import Mathlib

namespace Work.CORE4

theorem QOddCentMapCard {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (h : K ⊓ f.ker = ⊥) : Nat.card ↥(K.map f) = Nat.card ↥K := by
  -- The map `φ` sending `x : K` to `f x ∈ K.map f` is a bijection: it is injective
  -- because `K ⊓ ker f = ⊥`, and surjective by definition of the image subgroup.
  let φ : K → K.map f := fun x => ⟨f x, Subgroup.mem_map_of_mem f x.2⟩
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hxyeq : f (x : G) = f (y : G) := by simpa [φ] using congrArg Subtype.val hxy
    have hg : (x : G) * (y : G)⁻¹ = 1 := by
      have hmem : (x : G) * (y : G)⁻¹ ∈ K ⊓ f.ker := by
        have hyinv : (y : G)⁻¹ ∈ K := inv_mem y.2
        refine Subgroup.mem_inf.mpr ⟨mul_mem x.2 hyinv, ?_⟩
        exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxyeq, mul_inv_cancel])
      rw [h] at hmem
      exact Subgroup.mem_bot.mp hmem
    apply Subtype.ext
    have := congrArg (· * (y : G)) hg
    simpa [mul_assoc] using this
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact (Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)).symm

end Work.CORE4
