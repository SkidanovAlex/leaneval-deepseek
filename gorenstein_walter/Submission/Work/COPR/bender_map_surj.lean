import Mathlib

namespace Work.COPR

/-- **Bender map is surjective onto the "anti-fixed" elements.**

Let `X` be a finite group of odd order and `σ : X →* X` an endomorphism.
If `y` satisfies `σ y = y⁻¹` then `y` lies in the image of the Bender map
`x ↦ x⁻¹ * σ x`. Concretely, `x = y ^ (Nat.card X / 2)` is a preimage:
writing `N = Nat.card X` (odd) and `s = N / 2`, we have `2 * s + 1 = N`, hence
`y ^ N = 1` gives `y ^ (2 * s) = y ^ (N - 1) = y⁻¹`, and then
`x⁻¹ * σ x = (y⁻¹)^s * (y⁻¹)^s = (y⁻¹)^(2 * s) = (y ^ (2 * s))⁻¹
= (y⁻¹)⁻¹ = y`. -/
theorem bender_map_surj {X : Type*} [Group X] [Finite X] (σ : X →* X)
    (hodd : Odd (Nat.card X)) (y : X) (hy : σ y = y⁻¹) :
    ∃ x : X, x⁻¹ * σ x = y := by
  refine ⟨y ^ (Nat.card X / 2), ?_⟩
  have hNs : 2 * (Nat.card X / 2) + 1 = Nat.card X :=
    Nat.two_mul_div_two_add_one_of_odd hodd
  have hpow : y ^ Nat.card X = 1 := pow_card_eq_one'
  have hxinv : (y ^ (Nat.card X / 2))⁻¹ = (y⁻¹) ^ (Nat.card X / 2) := by
    rw [inv_pow]
  have hsig : σ (y ^ (Nat.card X / 2)) = (y⁻¹) ^ (Nat.card X / 2) := by
    rw [map_pow, hy]
  rw [hxinv, hsig]
  rw [← pow_add, ← two_mul]
  rw [inv_pow]
  have hNpos : 1 ≤ Nat.card X := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have h2s : 2 * (Nat.card X / 2) = Nat.card X - 1 := by omega
  rw [h2s]
  have hmul : y ^ (Nat.card X - 1) * y = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hNpos, hpow]
  exact inv_eq_of_mul_eq_one_right hmul

end Work.COPR
