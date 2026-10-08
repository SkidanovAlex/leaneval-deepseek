import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.ZassenhausSuzuki.SingerModelCycle

/-- If a subgroup `K` normalises a subgroup `H` and their intersection is trivial, then the
order of the join is the product of the orders: `|H ⊔ K| = |H| * |K|`.

The product map `↥H × ↥K → ↥(H ⊔ K)`, `(h, k) ↦ h * k`, is a bijection: it is surjective
because `H ⊔ K = H * K` as sets (valid since `K` normalises `H`), and injective because a
relation `h₁ * k₁ = h₂ * k₂` forces `h₂⁻¹ * h₁ = k₂ * k₁⁻¹`, an element of `H ⊓ K = ⊥`. -/
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

/-- Let `V ≤ G` be a subgroup of a finite group and `τ` an involution normalising `V` with
`τ ∉ V`.  Then the join `V ⊔ ⟨τ⟩` has order `2 * |V|`: it is the disjoint union of `V` and
`τ V`, since the induced map `V ⊔ ⟨τ⟩ → ZMod 2` is surjective with kernel `V`. -/
theorem card_sup_zpowers_of_inverts {G : Type*} [Group G] [Finite G]
    (V : Subgroup G) (τ : G) (hτ2 : τ * τ = 1) (hτV : τ ∉ V)
    (hconj : ∀ v ∈ V, τ * v * τ⁻¹ ∈ V) :
    Nat.card ↥(V ⊔ Subgroup.zpowers τ) = 2 * Nat.card ↥V := by
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left hτ2
  -- `τ` lies in the normalizer of `V`: conjugation by `τ` preserves `V` in both directions,
  -- the reverse direction provided by applying `hconj` twice.
  have hτmem : τ ∈ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj h hh, fun hh => ?_⟩
    have h2 := hconj (τ * h * τ⁻¹) hh
    have heq : τ * (τ * h * τ⁻¹) * τ⁻¹ = h := by
      rw [hτinv]
      calc τ * (τ * h * τ) * τ = (τ * τ) * h * (τ * τ) := by group
        _ = h := by rw [hτ2]; group
    rwa [heq] at h2
  have hle : Subgroup.zpowers τ ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.mpr hτmem
  -- `⟨τ⟩` has order `2` since `τ` is an involution different from `1`.
  have hτne : τ ≠ 1 := fun h => hτV (h ▸ V.one_mem)
  have hcard_zp : Nat.card ↥(Subgroup.zpowers τ) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hτ2) hτne
  -- `V ⊓ ⟨τ⟩ = ⊥`: its order divides `2`, and it cannot be the whole of `⟨τ⟩`.
  have hinf : V ⊓ Subgroup.zpowers τ = ⊥ := by
    have hdvd : Nat.card ↥(V ⊓ Subgroup.zpowers τ) ∣ 2 := by
      have h := Subgroup.card_dvd_of_le (H := V ⊓ Subgroup.zpowers τ)
        (K := Subgroup.zpowers τ) inf_le_right
      rwa [hcard_zp] at h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq (V ⊓ Subgroup.zpowers τ) h1
    · exfalso
      have hEq : V ⊓ Subgroup.zpowers τ = Subgroup.zpowers τ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right
          (le_of_eq (by rw [hcard_zp, h2]))
      have hmem : τ ∈ V ⊓ Subgroup.zpowers τ := hEq.symm ▸ Subgroup.mem_zpowers τ
      exact hτV (Subgroup.mem_inf.mp hmem).1
  have hmain := card_sup_of_inf_eq_bot_of_le_normalizer (H := V)
    (K := Subgroup.zpowers τ) hle hinf
  rw [hcard_zp, mul_comm] at hmain
  exact hmain

end Work.ZassenhausSuzuki.SingerModelCycle
