import Mathlib

namespace Work.KMTAreas.A7

/-- For `L ≥ 4`, `L ^ 2 ≤ 2 ^ L`. -/
private lemma pow_two_ge_sq : ∀ L : ℕ, 4 ≤ L → L ^ 2 ≤ 2 ^ L := by
  intro L
  induction L with
  | zero => intro hL; omega
  | succ n ih =>
      intro hn4
      rcases Nat.lt_or_ge n 4 with hn | hn
      · have hn3 : n = 3 := by omega
        subst hn3
        norm_num
      · have ihn : n ^ 2 ≤ 2 ^ n := ih hn
        calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
          _ ≤ 2 * 2 ^ n := by nlinarith
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- If `2 ^ L ≤ k * L + 1` and `1 ≤ k` then `L ≤ k + 1`. -/
private lemma log_le_succ_of_two_pow_le (k L : ℕ) (hk : 1 ≤ k) (h : 2 ^ L ≤ k * L + 1) :
    L ≤ k + 1 := by
  by_contra hc
  have hc' : k + 1 < L := not_le.mp hc
  have hLk : k + 2 ≤ L := by omega
  have hprod_le : L * (L - k) ≤ 1 := by
    rcases Nat.lt_or_ge L 4 with hlt | hge
    · have hL3 : L = 3 := by omega
      have hk1 : k = 1 := by omega
      subst hL3; subst hk1
      exact absurd h (by norm_num)
    · have hsq : L ^ 2 ≤ 2 ^ L := pow_two_ge_sq L hge
      have h1 : L ^ 2 ≤ k * L + 1 := le_trans hsq h
      rw [Nat.mul_comm k L] at h1
      have hh : L * (L - k) = L ^ 2 - (L * k) := by
        rw [Nat.mul_sub_left_distrib, pow_two]
      rw [hh]
      omega
  have hsub : 2 ≤ L - k := by omega
  have hpm : (k + 2) * 2 ≤ L * (L - k) := Nat.mul_le_mul hLk hsub
  omega

theorem ExcNumericBound (C₀ R : ℕ) (hC₀ : 1 ≤ C₀) (hR : 1 ≤ R)
    (h : R + 1 ≤ C₀ * Nat.log 2 (R + 2) + 2 * Nat.log 2 R) :
    R + 1 ≤ 8 * (C₀ + 2) ^ 2 + 64 ∧ C₀ * Nat.log 2 (R + 2) ≤ 8 * (C₀ + 2) ^ 2 + 64 := by
  have hk : 1 ≤ C₀ + 2 := by omega
  have hrL : Nat.log 2 R ≤ Nat.log 2 (R + 2) := Nat.log_mono_right (by omega)
  have h2L : 2 ^ Nat.log 2 (R + 2) ≤ R + 2 := Nat.pow_log_le_self 2 (by omega)
  have hRL : R + 1 ≤ (C₀ + 2) * Nat.log 2 (R + 2) := by
    have h2 : 2 * Nat.log 2 R ≤ 2 * Nat.log 2 (R + 2) := Nat.mul_le_mul_left 2 hrL
    calc R + 1 ≤ C₀ * Nat.log 2 (R + 2) + 2 * Nat.log 2 R := h
      _ ≤ C₀ * Nat.log 2 (R + 2) + 2 * Nat.log 2 (R + 2) := by omega
      _ = (C₀ + 2) * Nat.log 2 (R + 2) := by ring
  have hpow : 2 ^ Nat.log 2 (R + 2) ≤ (C₀ + 2) * Nat.log 2 (R + 2) + 1 := by
    calc 2 ^ Nat.log 2 (R + 2) ≤ R + 2 := h2L
      _ = (R + 1) + 1 := by ring
      _ ≤ (C₀ + 2) * Nat.log 2 (R + 2) + 1 := by omega
  have hL : Nat.log 2 (R + 2) ≤ C₀ + 2 + 1 := log_le_succ_of_two_pow_le (C₀ + 2) _ hk hpow
  have hkL : (C₀ + 2) * Nat.log 2 (R + 2) ≤ (C₀ + 2) * (C₀ + 3) :=
    Nat.mul_le_mul_left (C₀ + 2) hL
  have hmain : (C₀ + 2) * (C₀ + 3) ≤ 8 * (C₀ + 2) ^ 2 + 64 := by nlinarith
  constructor
  · linarith
  · have hle : C₀ ≤ C₀ + 2 := by omega
    have hCL : C₀ * Nat.log 2 (R + 2) ≤ (C₀ + 2) * Nat.log 2 (R + 2) :=
      Nat.mul_le_mul_right _ hle
    linarith

end Work.KMTAreas.A7
