import Mathlib
import Submission.Work.Peluse.LadderP.stepPCore

namespace Work.Peluse.LadderP

/-- The algebraic identity behind `finalConstLe`: writing `γ = u^D/4`, the right-hand side
`2·γ·(C·γ^E)^S` equals `2·C^S/4^(1+E·S) · u^(D·(1+E·S))`. -/
private lemma finalConstLe_key (u C : ℝ) (D E S : ℕ) :
    2 * (u ^ D / 4) * (C * (u ^ D / 4) ^ E) ^ S
      = 2 * C ^ S / 4 ^ (1 + E * S) * u ^ (D * (1 + E * S)) := by
  have h1 : (u ^ D / 4) ^ E = u ^ (D * E) / 4 ^ E := by rw [div_pow, ← pow_mul]
  rw [h1, mul_pow, div_pow, ← pow_mul, ← pow_mul]
  have hD : D * (1 + E * S) = D + D * E * S := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  field_simp
  rw [hD, pow_add, pow_add, pow_one]
  ring

/-- Pure real-arithmetic core: from `u ∈ (0,1]`, the exponent domination
`D·(1+E·S) ≤ e` and `C ≤ 2·C₅₁^S/4^(1+E·S)`, deduce
`C·u^e ≤ 2·γ·(C₅₁·γ^E)^S` where `γ = u^D/4`. -/
private lemma finalConstLe_core {u C C₅₁ γ : ℝ} {D E S e : ℕ}
    (hC : 0 < C)
    (hγ : γ = u ^ D / 4) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hege : D * (1 + E * S) ≤ e)
    (hCle : C ≤ 2 * C₅₁ ^ S / 4 ^ (1 + E * S)) :
    C * u ^ e ≤ 2 * γ * (C₅₁ * γ ^ E) ^ S := by
  have hu0' : (0 : ℝ) ≤ u := le_of_lt hu0
  have hpow : u ^ e ≤ u ^ (D * (1 + E * S)) :=
    pow_le_pow_of_le_one hu0' hu1 hege
  have hk : 0 ≤ 2 * C₅₁ ^ S / 4 ^ (1 + E * S) := le_trans (le_of_lt hC) hCle
  have hu : (0 : ℝ) ≤ u ^ e := pow_nonneg hu0' e
  calc C * u ^ e
      ≤ (2 * C₅₁ ^ S / 4 ^ (1 + E * S)) * u ^ e :=
        mul_le_mul_of_nonneg_right hCle hu
    _ ≤ (2 * C₅₁ ^ S / 4 ^ (1 + E * S)) * u ^ (D * (1 + E * S)) :=
        mul_le_mul_of_nonneg_left hpow hk
    _ = 2 * γ * (C₅₁ * γ ^ E) ^ S := by
        rw [hγ]
        exact (finalConstLe_key u C₅₁ D E S).symm

theorem finalConstLe (j n s' e₅₁ : ℕ) {C C₅₁ u γ : ℝ} {e : ℕ}
    (hC : 0 < C) (hC₅₁ : 0 < C₅₁) (he₅₁ : 1 ≤ e₅₁)
    (hγ : γ = u ^ (2 ^ (2 ^ (j+1) - 1 + n)) / 4) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hege : 2 ^ (2 ^ (j+1) - 1 + n) * (1 + e₅₁ * 2^s') ≤ e)
    (hCle : C ≤ 2 * C₅₁ ^ (2^s') / 4 ^ (1 + e₅₁ * 2^s')) :
    C * u ^ e ≤ 2 * γ * (C₅₁ * γ ^ e₅₁) ^ (2^s') := by
  have _ := hC
  have _ := hC₅₁
  have _ := he₅₁
  exact finalConstLe_core (D := 2 ^ (2 ^ (j+1) - 1 + n)) (E := e₅₁) (S := 2 ^ s')
    hC hγ hu0 hu1 hege hCle

end Work.Peluse.LadderP
