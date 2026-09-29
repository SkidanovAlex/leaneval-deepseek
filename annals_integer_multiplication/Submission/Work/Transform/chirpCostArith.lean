import Mathlib

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.Transform

/-- Concrete arithmetic bookkeeping for the cost of the Bluestein chirp-DFT pass (Prop. 3.5 of
Harvey--van der Hoeven, *Integer multiplication in time O(n log n)*): the linear-in-the-`K`-budget
expression on the left is dominated by `K * (T*p^2 + S*(p+1)^K) + K` as soon as `K` majorises
`10^6 (D+2)` times the total budget `Ks+…+Kr+2`, with `D = 1729`, `p ≥ 100` and `T ≥ 2^D`.

The proof extracts the common factor `W = T*p^2 + S*(p+1)^K ≥ 1`, bounds each monomial of the left
hand side by a small multiple of `W`, sums the resulting coefficients (which are bounded by
`24446 * (Ks+…+Kr+2)`) and finishes with `24446 * (Ks+…+Kr+2) ≤ 10^6 (D+2) * (Ks+…+Kr+2) ≤ K`. -/
theorem chirpCostArith (D T S tmax p Ks Kt Kb Kc Kd Kf Kr K : ℕ)
    (hD : D = 1729) (hp : 100 ≤ p) (hT : 2 ^ D ≤ T) (htS : tmax ≤ S) (htT : tmax ≤ T)
    (hK : 1000000 * (D + 2) * (Ks + Kt + Kb + Kc + Kd + Kf + Kr + 2) ≤ K) :
    (Ks * (S * (p + 1) ^ Ks) + Ks) +
      (D * (((Kr * 3 + Kb + 1) * (T * p ^ 2 + p + 1) + (Kt * (tmax * (p + 1) ^ Kt) + Kt + Kb)) +
        Kf * (p + 3)) + Kf) +
      (Kd * (T * (2 * p + 9) + 2) +
        (Kr * 3 * (T * (2 * p + 9) * 2 + 3 * (p + 2) + 2) +
          (Kc * (T * p ^ 2) + Kc + Kr * 3 * (T * (2 * p + 9) * 2 + 3 * (p + 2) + 2)))) ≤
    K * (T * p ^ 2 + S * (p + 1) ^ K) + K := by
  subst hD
  have hp1 : 1 ≤ p := by omega
  have hT1 : 1 ≤ T := by have := Nat.one_le_two_pow (n := 1729); omega
  have hp_sq : p ≤ p ^ 2 := by
    have := Nat.mul_le_mul_left p hp1
    simpa [pow_two] using this
  have hsq_le : p ^ 2 ≤ T * p ^ 2 := by
    have := Nat.mul_le_mul_right (p ^ 2) hT1
    simpa using this
  -- common factor
  set W := T * p ^ 2 + S * (p + 1) ^ K with hWdef
  have hXW : T * p ^ 2 ≤ W := by omega
  have hYW : S * (p + 1) ^ K ≤ W := by omega
  have hW1 : 1 ≤ W := by omega
  -- the budget
  set A := Ks + Kt + Kb + Kc + Kd + Kf + Kr + 2 with hAdef
  have hK' : 1000000 * (1729 + 2) * A ≤ K := by rw [hAdef]; exact hK
  have hpleW : p ≤ W := le_trans hp_sq (le_trans hsq_le hXW)
  have hTle0 : T ≤ T * p ^ 2 := by
    have h : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p (by omega)
    have := Nat.mul_le_mul_left T h
    simpa using this
  have hTleW : T ≤ W := le_trans hTle0 hXW
  have hTpleW : T * p ≤ W := by
    have h : T * p ≤ T * p ^ 2 := Nat.mul_le_mul_left T hp_sq
    exact le_trans h hXW
  -- elementary bounds on the geometric multipliers
  have hA4 : T * p ^ 2 + p + 1 ≤ 4 * W := by nlinarith only [hXW, hpleW, hW1]
  have hB13 : T * (2 * p + 9) + 2 ≤ 13 * W := by nlinarith only [hTpleW, hTleW, hW1]
  have hC40 : T * (2 * p + 9) * 2 + 3 * (p + 2) + 2 ≤ 40 * W := by
    nlinarith only [hTpleW, hTleW, hpleW, hW1]
  have hD4 : p + 3 ≤ 4 * W := by nlinarith only [hpleW, hW1]
  -- each budget variable is ≤ A, and A ≤ K
  have hA1 : 1 ≤ A := by omega
  have hKsA : Ks ≤ A := by omega
  have hKtA : Kt ≤ A := by omega
  have hKbA : Kb ≤ A := by omega
  have hKcA : Kc ≤ A := by omega
  have hKdA : Kd ≤ A := by omega
  have hKfA : Kf ≤ A := by omega
  have hKrA : Kr ≤ A := by omega
  have hA_le_K : A ≤ K := by
    have h1 : A ≤ 1000000 * (1729 + 2) * A := Nat.le_mul_of_pos_left A (by norm_num)
    omega
  have hKsK : Ks ≤ K := le_trans hKsA hA_le_K
  have hKtK : Kt ≤ K := le_trans hKtA hA_le_K
  have hpKs : (p + 1) ^ Ks ≤ (p + 1) ^ K := Nat.pow_le_pow_right (by omega) hKsK
  have hpKt : (p + 1) ^ Kt ≤ (p + 1) ^ K := Nat.pow_le_pow_right (by omega) hKtK
  -- termwise domination by a multiple of W
  have h1 : Ks * (S * (p + 1) ^ Ks) ≤ Ks * W :=
    Nat.mul_le_mul_left Ks (le_trans (Nat.mul_le_mul_left S hpKs) hYW)
  have h1b : Ks ≤ Ks * W := by simpa using Nat.mul_le_mul_left Ks hW1
  have h2a : (Kr * 3 + Kb + 1) * (T * p ^ 2 + p + 1) ≤ (Kr * 3 + Kb + 1) * (4 * W) :=
    Nat.mul_le_mul_left _ hA4
  have h2b : Kt * (tmax * (p + 1) ^ Kt) ≤ Kt * W :=
    Nat.mul_le_mul_left Kt (le_trans (Nat.mul_le_mul htS hpKt) hYW)
  have h2c : Kt + Kb ≤ (Kt + Kb) * W := by simpa using Nat.mul_le_mul_left (Kt + Kb) hW1
  have h2d : Kf * (p + 3) ≤ Kf * (4 * W) := Nat.mul_le_mul_left Kf hD4
  have h2e : Kf ≤ Kf * W := by simpa using Nat.mul_le_mul_left Kf hW1
  have h3a : Kd * (T * (2 * p + 9) + 2) ≤ Kd * (13 * W) := Nat.mul_le_mul_left Kd hB13
  have h3b : Kr * 3 * (T * (2 * p + 9) * 2 + 3 * (p + 2) + 2) ≤ Kr * 3 * (40 * W) :=
    Nat.mul_le_mul_left (Kr * 3) hC40
  have h3c : Kc * (T * p ^ 2) ≤ Kc * W := Nat.mul_le_mul_left Kc hXW
  have h3d : Kc ≤ Kc * W := by simpa using Nat.mul_le_mul_left Kc hW1
  -- assemble: left hand side ≤ (explicit coefficient) * W
  have hLHS : (Ks * (S * (p + 1) ^ Ks) + Ks) +
      (1729 * (((Kr * 3 + Kb + 1) * (T * p ^ 2 + p + 1) + (Kt * (tmax * (p + 1) ^ Kt) + Kt + Kb)) +
        Kf * (p + 3)) + Kf) +
      (Kd * (T * (2 * p + 9) + 2) +
        (Kr * 3 * (T * (2 * p + 9) * 2 + 3 * (p + 2) + 2) +
          (Kc * (T * p ^ 2) + Kc + Kr * 3 * (T * (2 * p + 9) * 2 + 3 * (p + 2) + 2)))) ≤
      (2 * Ks + 20988 * Kr + 8645 * Kb + 3458 * Kt + 6917 * Kf + 13 * Kd + 2 * Kc + 6916) * W := by
    nlinarith only [h1, h1b, h2a, h2b, h2c, h2d, h2e, h3a, h3b, h3c, h3d]
  have hCex : (2 * Ks + 20988 * Kr + 8645 * Kb + 3458 * Kt + 6917 * Kf + 13 * Kd + 2 * Kc + 6916)
      ≤ 24446 * A := by omega
  have hCW : (2 * Ks + 20988 * Kr + 8645 * Kb + 3458 * Kt + 6917 * Kf + 13 * Kd + 2 * Kc + 6916) * W
      ≤ (24446 * A) * W := Nat.mul_le_mul_right W hCex
  have hM : 24446 * A ≤ K := by
    have h1 : 24446 * A ≤ 1000000 * (1729 + 2) * A := Nat.mul_le_mul_right A (by norm_num)
    exact le_trans h1 hK'
  have hKW : (24446 * A) * W ≤ K * W := Nat.mul_le_mul_right W hM
  calc (Ks * (S * (p + 1) ^ Ks) + Ks) +
      (1729 * (((Kr * 3 + Kb + 1) * (T * p ^ 2 + p + 1) + (Kt * (tmax * (p + 1) ^ Kt) + Kt + Kb)) +
        Kf * (p + 3)) + Kf) +
      (Kd * (T * (2 * p + 9) + 2) +
        (Kr * 3 * (T * (2 * p + 9) * 2 + 3 * (p + 2) + 2) +
          (Kc * (T * p ^ 2) + Kc + Kr * 3 * (T * (2 * p + 9) * 2 + 3 * (p + 2) + 2))))
      ≤ (2 * Ks + 20988 * Kr + 8645 * Kb + 3458 * Kt + 6917 * Kf + 13 * Kd + 2 * Kc + 6916) * W := hLHS
    _ ≤ (24446 * A) * W := hCW
    _ ≤ K * W := hKW
    _ ≤ K * W + K := Nat.le_add_right _ _

end Work.Transform
