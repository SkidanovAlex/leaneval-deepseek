import Mathlib
import Submission.Work.Resample.buKit

namespace Work.Resample

/-!
# The cost inequalities for the uniform `B̃` preparation word

The word `prep` of `Work.Resample.buPrep` is built from `13` sub-words whose costs are bounded by
expressions of the shape `c * K * (p+1)^j` (a constant `c`, a "budget" integer `K` with `3K ≤ E`,
and a small power `j`), possibly multiplied by a factor `(t+1)` which the final estimate keeps.
`buAllCosts` collects all thirteen estimates at once: every one of them is at most
`(t+1) * (p+1)^E`, the cost budget of the whole word.

The mathematical content is the elementary fact that a fixed power of `p+1 ≥ 101` dwarfs both the
linear budget `K ≤ E/3` and any constant arising in the construction.

## Toolkit

* `le_pow_self_AC` : `K ≤ q^K` for `2 ≤ q`.
* `mul_pow_le_pow` : `K * q^K ≤ q^A` when `2K ≤ A` (the budget exponent is absorbed).
* `const_mul_mul_pow_le` : `C * K * q^j ≤ q^E` when `C ≤ q^c` and `c + K + j ≤ E`.
* `pow101` : `C ≤ q^n` from `C ≤ 101^n` and `101 ≤ q`.
-/

section Toolkit

/-- For `2 ≤ q` every natural number is at most `q` to its own power. -/
theorem le_pow_self_AC {q K : ℕ} (hq : 2 ≤ q) : K ≤ q ^ K := by
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h; simp
  · exact le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left hq K)

/-- If the exponent budget `A` is at least twice `K`, then `K * q^K ≤ q^A`: the linear factor `K`
is absorbed by the gap in the exponent. -/
theorem mul_pow_le_pow {q K A : ℕ} (hq : 2 ≤ q) (h : 2 * K ≤ A) : K * q ^ K ≤ q ^ A := by
  have hKA : K ≤ A - K := by omega
  have h1 : K ≤ q ^ (A - K) :=
    le_trans (le_pow_self_AC hq) (Nat.pow_le_pow_right (by omega : 0 < q) hKA)
  calc K * q ^ K ≤ q ^ (A - K) * q ^ K := Nat.mul_le_mul_right _ h1
    _ = q ^ A := by rw [← pow_add]; congr 1; omega

/-- A constant `C ≤ q^c` times a linear budget `K` times `q^j` is at most `q^E` whenever the
exponent budget `c + K + j` fits in `E`. -/
theorem const_mul_mul_pow_le {q E K C j c : ℕ} (hq : 2 ≤ q) (hC : C ≤ q ^ c)
    (hE : c + K + j ≤ E) : C * K * q ^ j ≤ q ^ E := by
  have hK : K ≤ q ^ (E - c - j) := by
    refine le_trans (le_pow_self_AC hq) (Nat.pow_le_pow_right (by omega : 0 < q) ?_)
    omega
  calc C * K * q ^ j ≤ q ^ c * K * q ^ j := by gcongr
    _ = K * q ^ (c + j) := by rw [pow_add]; ring
    _ ≤ q ^ (E - c - j) * q ^ (c + j) := Nat.mul_le_mul_right _ hK
    _ = q ^ E := by rw [← pow_add]; congr 1; omega

/-- Monotonicity of `q ↦ q^n` above the numerical threshold `101`. -/
theorem pow101 {q n C : ℕ} (hq : 101 ≤ q) (hC : C ≤ 101 ^ n) : C ≤ q ^ n :=
  le_trans hC (Nat.pow_le_pow_left hq n)

end Toolkit

/-- The arithmetic core of `buAllCosts`, stated for abstract `q = p+1`, `T = t+1`, `Z = buSZ p`,
`M = egM p α`, `N = egN p α s t`. -/
theorem buAllCostsCore (q T Z M N E s : ℕ) (hq : 101 ≤ q) (hT : 1 ≤ T) (hE : 100 ≤ E)
    (hs : s + 1 ≤ T) (hZ : Z + 1 ≤ q ^ 4) (hM : M + 1 ≤ q ^ 5) (hN : N + 1 ≤ q ^ 2)
    (KN KM KP Kroll Kdrop Kdup K11 K10 K9 K8 K7 : ℕ)
    (hKN : 3 * KN ≤ E) (hKM : 3 * KM ≤ E) (hKP : 3 * KP ≤ E) (hKr : 3 * Kroll ≤ E)
    (hKd : 3 * Kdrop ≤ E) (hKu : 3 * Kdup ≤ E) (hK11 : 3 * K11 ≤ E) (hK10 : 3 * K10 ≤ E)
    (hK9 : 3 * K9 ≤ E) (hK8 : 3 * K8 ≤ E) (hK7 : 3 * K7 ≤ E) :
    KN * q ^ KN ≤ T * q ^ E ∧
      4 * (Kroll * 5 * (5 * Z + 1)) ≤ T * q ^ E ∧
      KM * q ^ KM ≤ T * q ^ E ∧
      Kdup * (Z + 1) ≤ T * q ^ E ∧
      KP * q ^ KP ≤ T * q ^ E ∧
      6 * (Kroll * 7 * (7 * Z + 1)) ≤ T * q ^ E ∧
      K11 * (N + 1) * q ^ K11 ≤ T * q ^ E ∧
      K10 * (M + 1) * (s + 1) * q ^ K10 ≤ T * q ^ E ∧
      K9 * (s + 1) * q ^ K9 ≤ T * q ^ E ∧
      K8 * (s + 1) * q ^ K8 ≤ T * q ^ E ∧
      K7 * T * q ^ K7 ≤ T * q ^ E ∧
      7 * (Kroll * 8 * (8 * (2 * (T * q ^ 20)) + 1)) ≤ T * q ^ E ∧
      Kroll * 7 * (7 * Z + 1) + Kdrop * (Z + 1) ≤ T * q ^ E := by
  have hq2 : 2 ≤ q := by omega
  have hTpos : 0 < T := by omega
  have hq4 : 1 ≤ q ^ 4 := by have := pow_pos (by omega : 0 < q) 4; omega
  have hq20 : 1 ≤ q ^ 20 := by have := pow_pos (by omega : 0 < q) 20; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc KN * q ^ KN ≤ q ^ E := mul_pow_le_pow hq2 (by omega)
      _ ≤ T * q ^ E := Nat.le_mul_of_pos_left _ hTpos
  · have h1 : 4 * (Kroll * 5 * (5 * Z + 1)) ≤ 100 * Kroll * q ^ 4 := by
      calc 4 * (Kroll * 5 * (5 * Z + 1)) ≤ 4 * (Kroll * 5 * (5 * q ^ 4)) := by gcongr; omega
        _ = 100 * Kroll * q ^ 4 := by ring
    calc 4 * (Kroll * 5 * (5 * Z + 1)) ≤ 100 * Kroll * q ^ 4 := h1
      _ ≤ q ^ E := const_mul_mul_pow_le (q := q) (E := E) (K := Kroll) (C := 100) (j := 4) (c := 10)
          hq2 (pow101 hq (by norm_num)) (by omega)
      _ ≤ T * q ^ E := Nat.le_mul_of_pos_left _ hTpos
  · calc KM * q ^ KM ≤ q ^ E := mul_pow_le_pow hq2 (by omega)
      _ ≤ T * q ^ E := Nat.le_mul_of_pos_left _ hTpos
  · calc Kdup * (Z + 1) ≤ Kdup * q ^ 4 := Nat.mul_le_mul_left _ hZ
      _ ≤ q ^ E := by
          simpa using (const_mul_mul_pow_le (q := q) (E := E) (K := Kdup) (C := 1) (j := 4) (c := 0)
            hq2 (by simp) (by omega))
      _ ≤ T * q ^ E := Nat.le_mul_of_pos_left _ hTpos
  · calc KP * q ^ KP ≤ q ^ E := mul_pow_le_pow hq2 (by omega)
      _ ≤ T * q ^ E := Nat.le_mul_of_pos_left _ hTpos
  · have h1 : 6 * (Kroll * 7 * (7 * Z + 1)) ≤ 294 * Kroll * q ^ 4 := by
      calc 6 * (Kroll * 7 * (7 * Z + 1)) ≤ 6 * (Kroll * 7 * (7 * q ^ 4)) := by gcongr; omega
        _ = 294 * Kroll * q ^ 4 := by ring
    calc 6 * (Kroll * 7 * (7 * Z + 1)) ≤ 294 * Kroll * q ^ 4 := h1
      _ ≤ q ^ E := const_mul_mul_pow_le (q := q) (E := E) (K := Kroll) (C := 294) (j := 4) (c := 10)
          hq2 (pow101 hq (by norm_num)) (by omega)
      _ ≤ T * q ^ E := Nat.le_mul_of_pos_left _ hTpos
  · have h1 : K11 * (N + 1) * q ^ K11 ≤ K11 * q ^ K11 * q ^ 2 := by
      calc K11 * (N + 1) * q ^ K11 ≤ K11 * q ^ 2 * q ^ K11 := by gcongr
        _ = K11 * q ^ K11 * q ^ 2 := by ring
    have h2 : K11 * q ^ K11 ≤ q ^ (E - 2) := mul_pow_le_pow hq2 (by omega)
    have h3 : q ^ (E - 2) * q ^ 2 = q ^ E := by rw [← pow_add]; congr 1; omega
    calc K11 * (N + 1) * q ^ K11 ≤ K11 * q ^ K11 * q ^ 2 := h1
      _ ≤ q ^ (E - 2) * q ^ 2 := Nat.mul_le_mul_right _ h2
      _ = q ^ E := h3
      _ ≤ T * q ^ E := Nat.le_mul_of_pos_left _ hTpos
  · have h1 : K10 * (M + 1) * (s + 1) * q ^ K10 ≤ T * (K10 * q ^ K10 * q ^ 5) := by
      calc K10 * (M + 1) * (s + 1) * q ^ K10 ≤ K10 * q ^ 5 * T * q ^ K10 := by gcongr
        _ = T * (K10 * q ^ K10 * q ^ 5) := by ring
    have h2 : K10 * q ^ K10 ≤ q ^ (E - 5) := mul_pow_le_pow hq2 (by omega)
    have h3 : q ^ (E - 5) * q ^ 5 = q ^ E := by rw [← pow_add]; congr 1; omega
    calc K10 * (M + 1) * (s + 1) * q ^ K10 ≤ T * (K10 * q ^ K10 * q ^ 5) := h1
      _ ≤ T * (q ^ (E - 5) * q ^ 5) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
      _ = T * q ^ E := by rw [h3]
  · have h1 : K9 * (s + 1) * q ^ K9 ≤ T * (K9 * q ^ K9) := by
      calc K9 * (s + 1) * q ^ K9 ≤ K9 * T * q ^ K9 := by gcongr
        _ = T * (K9 * q ^ K9) := by ring
    calc K9 * (s + 1) * q ^ K9 ≤ T * (K9 * q ^ K9) := h1
      _ ≤ T * q ^ E := Nat.mul_le_mul_left _ (mul_pow_le_pow hq2 (by omega))
  · have h1 : K8 * (s + 1) * q ^ K8 ≤ T * (K8 * q ^ K8) := by
      calc K8 * (s + 1) * q ^ K8 ≤ K8 * T * q ^ K8 := by gcongr
        _ = T * (K8 * q ^ K8) := by ring
    calc K8 * (s + 1) * q ^ K8 ≤ T * (K8 * q ^ K8) := h1
      _ ≤ T * q ^ E := Nat.mul_le_mul_left _ (mul_pow_le_pow hq2 (by omega))
  · calc K7 * T * q ^ K7 = T * (K7 * q ^ K7) := by ring
      _ ≤ T * q ^ E := Nat.mul_le_mul_left _ (mul_pow_le_pow hq2 (by omega))
  · have h1a : 8 * (2 * (T * q ^ 20)) + 1 ≤ 17 * (T * q ^ 20) := by
      have hx : 1 ≤ T * q ^ 20 := one_le_mul hT hq20
      linarith
    have h1 : 7 * (Kroll * 8 * (8 * (2 * (T * q ^ 20)) + 1)) ≤ 952 * Kroll * q ^ 20 * T := by
      calc 7 * (Kroll * 8 * (8 * (2 * (T * q ^ 20)) + 1)) ≤ 7 * (Kroll * 8 * (17 * (T * q ^ 20))) := by
            gcongr
        _ = 952 * Kroll * q ^ 20 * T := by ring
    have h2 : 952 * Kroll * q ^ 20 ≤ q ^ E :=
      const_mul_mul_pow_le (q := q) (E := E) (K := Kroll) (C := 952) (j := 20) (c := 10)
        hq2 (pow101 hq (by norm_num)) (by omega)
    calc 7 * (Kroll * 8 * (8 * (2 * (T * q ^ 20)) + 1)) ≤ 952 * Kroll * q ^ 20 * T := h1
      _ ≤ q ^ E * T := Nat.mul_le_mul_right _ h2
      _ = T * q ^ E := by ring
  · have h1 : Kroll * 7 * (7 * Z + 1) + Kdrop * (Z + 1) ≤ (56 * Kroll + Kdrop) * q ^ 4 := by
      nlinarith [hZ, hq4]
    have h2 : 56 * Kroll ≤ q ^ (E - 5) := by
      have ha : 56 * Kroll ≤ q ^ 2 * q ^ Kroll :=
        Nat.mul_le_mul (pow101 hq (by norm_num : 56 ≤ 101 ^ 2)) (le_pow_self_AC hq2)
      have hb : q ^ 2 * q ^ Kroll = q ^ (Kroll + 2) := by rw [pow_add]; ring
      have hc : q ^ (Kroll + 2) ≤ q ^ (E - 5) := Nat.pow_le_pow_right (by omega) (by omega)
      exact le_trans (le_trans ha (le_of_eq hb)) hc
    have h3 : Kdrop ≤ q ^ (E - 5) :=
      le_trans (le_pow_self_AC hq2) (Nat.pow_le_pow_right (by omega) (by omega))
    have h4 : 56 * Kroll + Kdrop ≤ q ^ (E - 4) := by
      have h5 := add_le_add h2 h3
      have h6 : q ^ (E - 5) + q ^ (E - 5) ≤ q * q ^ (E - 5) := by
        have : q ^ (E - 5) + q ^ (E - 5) = 2 * q ^ (E - 5) := by ring
        rw [this]
        exact Nat.mul_le_mul_right _ hq2
      have h7 : q * q ^ (E - 5) = q ^ (E - 4) := by
        have : q * q ^ (E - 5) = q ^ 1 * q ^ (E - 5) := by rw [pow_one]
        rw [this, ← pow_add]; congr 1; omega
      exact le_trans h5 (le_trans h6 (le_of_eq h7))
    calc Kroll * 7 * (7 * Z + 1) + Kdrop * (Z + 1) ≤ (56 * Kroll + Kdrop) * q ^ 4 := h1
      _ ≤ q ^ (E - 4) * q ^ 4 := Nat.mul_le_mul_right _ h4
      _ = q ^ E := by rw [← pow_add]; congr 1; omega
      _ ≤ T * q ^ E := Nat.le_mul_of_pos_left _ hTpos

theorem buAllCosts (p t E : ℕ) (hp : 100 ≤ p) (hE : 100 ≤ E)
    (α s : ℕ) (hs : s + 1 ≤ t + 1) (hα : Work.Resample.egM p α + 1 ≤ (p + 1) ^ 5)
    (hBK : Work.Resample.buSZ p + 1 ≤ (p + 1) ^ 4)
    (hN : Work.Resample.egN p α s t + 1 ≤ (p + 1) ^ 2)
    (KN KM KP Kroll Kdrop Kdup K11 K10 K9 K8 K7 : ℕ)
    (hKN : 3 * KN ≤ E) (hKM : 3 * KM ≤ E) (hKP : 3 * KP ≤ E) (hKr : 3 * Kroll ≤ E)
    (hKd : 3 * Kdrop ≤ E) (hKu : 3 * Kdup ≤ E) (hK11 : 3 * K11 ≤ E) (hK10 : 3 * K10 ≤ E)
    (hK9 : 3 * K9 ≤ E) (hK8 : 3 * K8 ≤ E) (hK7 : 3 * K7 ≤ E) :
    KN * (p + 1) ^ KN ≤ (t + 1) * (p + 1) ^ E ∧
    4 * (Kroll * 5 * (5 * Work.Resample.buSZ p + 1)) ≤ (t + 1) * (p + 1) ^ E ∧
    KM * (p + 1) ^ KM ≤ (t + 1) * (p + 1) ^ E ∧
    Kdup * (Work.Resample.buSZ p + 1) ≤ (t + 1) * (p + 1) ^ E ∧
    KP * (p + 1) ^ KP ≤ (t + 1) * (p + 1) ^ E ∧
    6 * (Kroll * 7 * (7 * Work.Resample.buSZ p + 1)) ≤ (t + 1) * (p + 1) ^ E ∧
    K11 * (Work.Resample.egN p α s t + 1) * (p + 1) ^ K11 ≤ (t + 1) * (p + 1) ^ E ∧
    K10 * (Work.Resample.egM p α + 1) * (s + 1) * (p + 1) ^ K10 ≤ (t + 1) * (p + 1) ^ E ∧
    K9 * (s + 1) * (p + 1) ^ K9 ≤ (t + 1) * (p + 1) ^ E ∧
    K8 * (s + 1) * (p + 1) ^ K8 ≤ (t + 1) * (p + 1) ^ E ∧
    K7 * (t + 1) * (p + 1) ^ K7 ≤ (t + 1) * (p + 1) ^ E ∧
    7 * (Kroll * 8 * (8 * (2 * ((t + 1) * (p + 1) ^ 20)) + 1)) ≤ (t + 1) * (p + 1) ^ E ∧
    (Kroll * 7 * (7 * Work.Resample.buSZ p + 1) + Kdrop * (Work.Resample.buSZ p + 1) ≤
      (t + 1) * (p + 1) ^ E) := by
  exact buAllCostsCore (p + 1) (t + 1) (buSZ p) (egM p α) (egN p α s t) E s
    (by omega) (by omega) hE hs hBK hα hN KN KM KP Kroll Kdrop Kdup K11 K10 K9 K8 K7
    hKN hKM hKP hKr hKd hKu hK11 hK10 hK9 hK8 hK7

end Work.Resample
