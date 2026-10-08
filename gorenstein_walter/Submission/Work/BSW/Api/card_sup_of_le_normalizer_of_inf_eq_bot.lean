import Mathlib

namespace Work.BSW.Api

open scoped Pointwise

theorem card_sup_of_le_normalizer_of_inf_eq_bot {G : Type} [Group G] [Finite G]
    {H K : Subgroup G} (hn : K ≤ Subgroup.normalizer (H : Set G)) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  -- `K` normalizes `H`, so `H ⊔ K = H * K` as sets.
  have hcoe : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H K hn
  -- `H` and `K` meet trivially, so multiplication is injective on `H × K`.
  have hdj : Disjoint H K := disjoint_iff.mpr hd
  -- Multiplication `H × K → ↥(H ⊔ K)` is a bijection.
  have hbij : Function.Bijective
      (fun x : H × K => (⟨(x.1 : G) * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥(H ⊔ K))) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact Subgroup.mul_injective_of_disjoint hdj (Subtype.ext_iff.mp hxy)
    · intro z
      have hz : (z : G) ∈ (H : Set G) * (K : Set G) := hcoe ▸ z.2
      obtain ⟨h, hh, k, hk, hk_eq⟩ := Set.mem_mul.mp hz
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hk_eq⟩
  calc Nat.card ↥(H ⊔ K) = Nat.card (H × K) := Nat.card_congr (Equiv.ofBijective _ hbij).symm
    _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod _ _

end Work.BSW.Api
