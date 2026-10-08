import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- For `q ≥ 3` we have `q < 2 ^ (q - 1)`. -/
private lemma lt_two_pow_pred (q : ℕ) (hq : 3 ≤ q) : q < 2 ^ (q - 1) := by
  have hmain : ∀ n, 2 ≤ n → n + 1 < 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
      rw [hpow]
      have h1 : m + 1 + 1 ≤ 2 * (m + 1) := by omega
      have h2 : 2 * (m + 1) < 2 ^ m * 2 := by
        have := Nat.mul_lt_mul_of_pos_right ih (by norm_num : (0:ℕ) < 2)
        nlinarith [this]
      omega
  have := hmain (q - 1) (by omega)
  omega

/-- For `D ≥ 3` we have `2 ≤ D.totient`. -/
private lemma two_le_totient (D : ℕ) (hD : 3 ≤ D) : 2 ≤ D.totient := by
  have hpos : 0 < D.totient := by rw [Nat.totient_pos]; omega
  have hev : Even D.totient := Nat.totient_even (by omega)
  obtain ⟨k, hk⟩ := hev
  omega

lemma pow_arith {q D j : ℕ} (hq3 : 3 ≤ q) (hD2 : 2 ≤ D) (hDle : D ≤ q - 1)
    (hj : 1 ≤ j) (hcase : j = 1 → 3 ≤ D) :
    q * 2 ^ (D * q ^ (j - 1)) < 2 ^ ((q ^ j - 1) * D.totient) := by
  have hqpos : 0 < q := by omega
  have hq_ge1 : 1 ≤ q := by omega
  have hphi_pos : 0 < D.totient := by rw [Nat.totient_pos]; omega
  have hphi_ge1 : 1 ≤ D.totient := hphi_pos
  -- The key arithmetic bound: `D * q ^ (j - 1) + (q - 1) ≤ (q ^ j - 1) * φ(D)`.
  have hbound : D * q ^ (j - 1) + (q - 1) ≤ (q ^ j - 1) * D.totient := by
    rcases eq_or_lt_of_le hj with h1 | h2
    · -- case `j = 1`
      subst h1
      have hD3 : 3 ≤ D := hcase rfl
      have hphi2 : 2 ≤ D.totient := two_le_totient D hD3
      simp only [Nat.sub_self, pow_zero, pow_one, mul_one]
      calc D + (q - 1) ≤ (q - 1) + (q - 1) := by omega
        _ = (q - 1) * 2 := by ring
        _ ≤ (q - 1) * D.totient := Nat.mul_le_mul_left _ hphi2
    · -- case `2 ≤ j`
      have hqa : q ≤ q ^ (j - 1) := by
        have h1 : 1 ≤ j - 1 := by omega
        calc q = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ (j - 1) := pow_le_pow_right' hq_ge1 h1
      have hqj : q ^ j = q ^ (j - 1) * q := by
        conv_lhs => rw [← Nat.sub_add_cancel hj]
        rw [pow_add, pow_one]
      have hkey : D * q ^ (j - 1) + q ≤ q ^ j := by
        have hq_eq : q = (q - 1) + 1 := (Nat.succ_pred_eq_of_pos hqpos).symm
        nlinarith [hqj, hDle, hqa, hq_eq]
      have hle1 : D * q ^ (j - 1) + (q - 1) ≤ q ^ j - 1 := by omega
      calc D * q ^ (j - 1) + (q - 1) ≤ q ^ j - 1 := hle1
        _ ≤ (q ^ j - 1) * D.totient := by
            have := Nat.mul_le_mul_left (q ^ j - 1) hphi_ge1
            simpa using this
  -- `q < 2 ^ (q - 1)`.
  have hqpow : q < 2 ^ (q - 1) := lt_two_pow_pred q hq3
  have hsub : q - 1 ≤ (q ^ j - 1) * D.totient - D * q ^ (j - 1) := by omega
  have h2 : q < 2 ^ ((q ^ j - 1) * D.totient - D * q ^ (j - 1)) :=
    lt_of_lt_of_le hqpow (pow_le_pow_right' (by norm_num : (1:ℕ) ≤ 2) hsub)
  calc q * 2 ^ (D * q ^ (j - 1))
      < 2 ^ ((q ^ j - 1) * D.totient - D * q ^ (j - 1)) * 2 ^ (D * q ^ (j - 1)) :=
        Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
    _ = 2 ^ (((q ^ j - 1) * D.totient - D * q ^ (j - 1)) + D * q ^ (j - 1)) :=
        (pow_add 2 _ _).symm
    _ = 2 ^ ((q ^ j - 1) * D.totient) := by
        congr 1
        omega

end Work.PGroup
