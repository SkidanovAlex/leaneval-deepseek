import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Commons.GroupTheory.Subgroup

/-- If `K` is contained in the normalizer of `H` and `H ⊓ K = ⊥`, then the multiplication map
`H × K → H ⊔ K` is a bijection, so `|H ⊔ K| = |H| * |K|`.  No finiteness hypothesis is
needed: `Nat.card` is `0` on infinite types and both sides vanish consistently. -/
theorem card_sup_of_inf_eq_bot_of_le_normalizer {G : Type*} [Group G] (H K : Subgroup G)
    (hK : K ≤ Subgroup.normalizer (H : Set G)) (hinf : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  have hcoe : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H K hK
  let f : ↥H × ↥K → ↥(H ⊔ K) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨h1, k1⟩ ⟨h2, k2⟩ heq
      have heq' : (h1 : G) * (k1 : G) = (h2 : G) * (k2 : G) := by
        simpa [f] using congrArg Subtype.val heq
      have hh2 : (h2 : G)⁻¹ * h1 = (k2 : G) * (k1 : G)⁻¹ := by
        have key : (h2 : G)⁻¹ * h1 * (k1 : G) = (k2 : G) := by
          rw [mul_assoc, heq', inv_mul_cancel_left]
        rw [show (h2 : G)⁻¹ * h1 = ((h2 : G)⁻¹ * h1 * (k1 : G)) * (k1 : G)⁻¹ from by group,
          key]
      have hmem : (h2 : G)⁻¹ * h1 ∈ H ⊓ K := by
        constructor
        · exact H.mul_mem (H.inv_mem h2.2) h1.2
        · rw [hh2]
          exact K.mul_mem k2.2 (K.inv_mem k1.2)
      rw [hinf, Subgroup.mem_bot] at hmem
      have hh : (h1 : G) = (h2 : G) := by
        calc (h1 : G) = (h2 : G) * ((h2 : G)⁻¹ * h1) := by group
          _ = (h2 : G) * 1 := by rw [hmem]
          _ = (h2 : G) := by group
      have hk : (k1 : G) = (k2 : G) := by
        have h2' : (k2 : G) * (k1 : G)⁻¹ = 1 := hh2 ▸ hmem
        calc (k1 : G) = ((k2 : G) * (k1 : G)⁻¹) * (k1 : G) := by rw [h2']; group
          _ = (k2 : G) := by group
      exact Prod.ext (Subtype.ext hh) (Subtype.ext hk)
    · intro x
      have hx : (x : G) ∈ (H : Set G) * (K : Set G) := by
        rw [← hcoe]; exact x.2
      obtain ⟨h, hh, k, hk, hk_eq⟩ := Set.mem_mul.mp hx
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext (by simpa [f] using hk_eq)⟩
  calc Nat.card ↥(H ⊔ K) = Nat.card (↥H × ↥K) := (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod _ _

end Commons.GroupTheory.Subgroup