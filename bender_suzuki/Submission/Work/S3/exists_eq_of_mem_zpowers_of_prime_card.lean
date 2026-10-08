import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.S3

set_option linter.style.haveILetI false

/-- If `P` is a finite group of prime order `p`, `Φ` is an element with `Φ ^ p = 1`, and an
injective homomorphism `γ : P →* A` has image contained in the cyclic subgroup `⟨Φ⟩`, then `Φ`
lies in the image of `γ`. -/
theorem exists_eq_of_mem_zpowers_of_prime_card {A : Type} [Group A] {P : Type} [Group P] [Finite P]
    (hp : (Nat.card P).Prime) (Φ : A) (hΦ : Φ ^ Nat.card P = 1)
    (γ : P →* A) (hγ : Function.Injective γ)
    (hmem : ∀ a : P, γ a ∈ Subgroup.zpowers Φ) : ∃ a : P, γ a = Φ := by
  -- `Φ` has finite order, so `⟨Φ⟩` is a finite group.
  haveI hfin : Finite (Subgroup.zpowers Φ : Subgroup A) :=
    Finite.of_equiv (Fin (orderOf Φ))
      (finEquivZPowers (isOfFinOrder_iff_pow_eq_one.mpr ⟨Nat.card P, hp.pos, hΦ⟩))
  -- The image of `γ` is a subgroup of `⟨Φ⟩`.
  have hle : Subgroup.map γ ⊤ ≤ Subgroup.zpowers Φ := by
    rw [Subgroup.map_le_iff_le_comap]
    exact fun x _ => hmem x
  -- Cardinality of the image is `Nat.card P`.
  have hcardK : Nat.card (Subgroup.map γ ⊤) = Nat.card P := by
    rw [Subgroup.card_map_of_injective hγ, Subgroup.card_top]
  -- Cardinality of `⟨Φ⟩` is `orderOf Φ`, which divides `Nat.card P`.
  have hcardH : Nat.card (Subgroup.zpowers Φ : Subgroup A) = orderOf Φ := Nat.card_zpowers Φ
  have hdvd : orderOf Φ ∣ Nat.card P := orderOf_dvd_iff_pow_eq_one.mpr hΦ
  have hcardle : Nat.card (Subgroup.zpowers Φ : Subgroup A) ≤ Nat.card (Subgroup.map γ ⊤) := by
    rw [hcardH, hcardK]
    exact Nat.le_of_dvd hp.pos hdvd
  -- Hence the image equals `⟨Φ⟩`, and `Φ` is in the image.
  have heq : Subgroup.map γ ⊤ = Subgroup.zpowers Φ := Subgroup.eq_of_le_of_card_ge hle hcardle
  have hmemΦ : Φ ∈ Subgroup.map γ ⊤ := by
    rw [heq]
    exact Subgroup.mem_zpowers Φ
  rw [Subgroup.mem_map] at hmemΦ
  obtain ⟨x, -, hx⟩ := hmemΦ
  exact ⟨x, hx⟩

end Work.S3
