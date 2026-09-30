import Mathlib
import Submission.Work.BMF.adi_const

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- Elementary estimate: `k + 1 ≤ 3 ^ (2k+2)`. -/
private lemma kp1_le_three_pow (k : ℕ) : k + 1 ≤ 3 ^ (2 * k + 2) := by
  have h1 : k + 1 ≤ 2 ^ (k + 1) := by
    have hlt := Nat.lt_two_pow_self (n := k)
    calc k + 1 ≤ 2 ^ k + 1 := by omega
      _ ≤ 2 ^ k * 2 := by
          have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          omega
      _ = 2 ^ (k + 1) := by ring
  have h2 : 2 ^ (k + 1) ≤ 3 ^ (2 * k + 2) := by
    calc 2 ^ (k + 1) ≤ 3 ^ (k + 1) := Nat.pow_le_pow_left (by norm_num) _
      _ ≤ 3 ^ (2 * k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  linarith

/-- The exponent identity underlying `K_absorb`: the exponent on the right-hand side is
`Eexp k + 2k + 2`. -/
private lemma Kc_sub_eq (k : ℕ) : Kc k - K0c k - k - 1 = Eexp k + 2 * k + 2 := by
  unfold Kc; omega

theorem K_absorb (k : ℕ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) {Z : ℝ} (hZ : (C₀ + 2) ^ 3 ≤ Z) :
    ((k : ℝ) + 1) * C1c k C₀ * C₀ ^ k ≤ Z ^ (Kc k - K0c k - k - 1) := by
  have hC0le : (0 : ℝ) ≤ C₀ := by linarith
  have hA3 : (3 : ℝ) ≤ C₀ + 2 := by linarith
  have hAle : (0 : ℝ) ≤ C₀ + 2 := by linarith
  have hA1 : (1 : ℝ) ≤ C₀ + 2 := by linarith
  have heq := Kc_sub_eq k
  -- `(k+1) ≤ (C₀+2)^(2k+2)`
  have step1 : ((k : ℝ) + 1) ≤ (C₀ + 2) ^ (2 * k + 2) := by
    have h3 : ((k : ℝ) + 1) ≤ (3 : ℝ) ^ (2 * k + 2) := by
      exact_mod_cast kp1_le_three_pow k
    have h34 : (3 : ℝ) ^ (2 * k + 2) ≤ (C₀ + 2) ^ (2 * k + 2) :=
      pow_le_pow_left₀ (by norm_num) hA3 _
    linarith
  -- `C₀^k ≤ (C₀+2)^k`
  have step2 : C₀ ^ k ≤ (C₀ + 2) ^ k := pow_le_pow_left₀ hC0le (by linarith) k
  -- `(k+1) * C₀^k ≤ (C₀+2)^(3k+2)`
  have hmul : ((k : ℝ) + 1) * C₀ ^ k ≤ (C₀ + 2) ^ (3 * k + 2) := by
    have h := mul_le_mul step1 step2 (pow_nonneg hC0le k) (pow_nonneg hAle (2 * k + 2))
    have hcomb : (C₀ + 2) ^ (2 * k + 2) * (C₀ + 2) ^ k = (C₀ + 2) ^ (3 * k + 2) := by
      rw [← pow_add]; congr 1; ring
    rwa [hcomb] at h
  have h1 : ((k : ℝ) + 1) * C₀ ^ k * (C₀ + 2) ^ (Eexp k)
      ≤ (C₀ + 2) ^ (3 * k + 2) * (C₀ + 2) ^ (Eexp k) :=
    mul_le_mul_of_nonneg_right hmul (pow_nonneg hAle _)
  -- absorb `(C₀+2)^(Eexp k)` and use `Z ≥ (C₀+2)^3`
  have h2 : (C₀ + 2) ^ (3 * k + 2) * (C₀ + 2) ^ (Eexp k) ≤ Z ^ (Eexp k + 2 * k + 2) := by
    rw [← pow_add]
    have hmono : (C₀ + 2) ^ (3 * k + 2 + Eexp k) ≤ (C₀ + 2) ^ (3 * (Eexp k + 2 * k + 2)) :=
      pow_le_pow_right₀ hA1 (by omega)
    have hZpow' : (C₀ + 2) ^ (3 * (Eexp k + 2 * k + 2)) ≤ Z ^ (Eexp k + 2 * k + 2) := by
      calc (C₀ + 2) ^ (3 * (Eexp k + 2 * k + 2))
          = ((C₀ + 2) ^ 3) ^ (Eexp k + 2 * k + 2) := by rw [pow_mul]
        _ ≤ Z ^ (Eexp k + 2 * k + 2) := pow_le_pow_left₀ (pow_nonneg hAle 3) hZ _
    linarith
  calc ((k : ℝ) + 1) * C1c k C₀ * C₀ ^ k
      = ((k : ℝ) + 1) * C₀ ^ k * (C₀ + 2) ^ (Eexp k) := by unfold C1c; ring
    _ ≤ (C₀ + 2) ^ (3 * k + 2) * (C₀ + 2) ^ (Eexp k) := h1
    _ ≤ Z ^ (Eexp k + 2 * k + 2) := h2
    _ = Z ^ (Kc k - K0c k - k - 1) := by rw [heq]

end Work.BMF
