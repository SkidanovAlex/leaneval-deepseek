import Mathlib

namespace Work.CORE4.A7FGB

open scoped Pointwise

/-- If `A` normalizes `B` and `A ⊓ B = ⊥`, then `A ⊔ B = A · B` as sets, and multiplication
`A × B → A ⊔ B` is a bijection, whence `|A ⊔ B| = |A| * |B|`. -/
theorem card_sup_of_inf_eq_bot {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  -- `A` normalizes `B`, so `A ⊔ B` is the set of products `a * b` with `a ∈ A`, `b ∈ B`.
  have hcoe : (↑(A ⊔ B) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
  -- Trivial intersection makes this product decomposition unique.
  have hdj : Disjoint A B := disjoint_iff.mpr h
  have hbij : Function.Bijective
      (fun p : ↥A × ↥B =>
        (⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B))) := by
    refine ⟨?_, ?_⟩
    · intro p q hpq
      have hpq' : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := Subtype.ext_iff.mp hpq
      exact Subgroup.mul_injective_of_disjoint hdj hpq'
    · intro z
      have hz : (z : G) ∈ (A : Set G) * (B : Set G) := by
        rw [← hcoe]; exact z.2
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hz
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc Nat.card ↥(A ⊔ B) = Nat.card (↥A × ↥B) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card ↥A * Nat.card ↥B := Nat.card_prod _ _

end Work.CORE4.A7FGB
