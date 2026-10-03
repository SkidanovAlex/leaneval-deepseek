import Mathlib

set_option linter.unusedVariables false

namespace Work.Analysis.IonescuWainger

/-- Elementary arithmetic fact: for `n ≥ 2`, `n + 2 ≤ 2 ^ n`. -/
private lemma two_pow_add_two_le : ∀ n : ℕ, 2 ≤ n → n + 2 ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro h
    by_cases hm : 2 ≤ m
    · have ihm := ih hm
      have hp : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have he : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by
        rw [Nat.pow_succ, mul_comm, two_mul]
      omega
    · have hm1 : m = 1 := by omega
      subst hm1
      norm_num

/-- If `p` is a prime with `p ≤ N`, `ε ∈ (0,1/2]` and `2 ^ ((1+ε)/ε) ≤ N`, then
`N ≤ p ^ ((1+ε) * ⌊N/p⌋)`.  (The proof only uses `ε > 0`, `N ≥ 8` and the bound on
`2 ^ ((1+ε)/ε)`; the condition `ε ≤ 1/2` is part of the caller's setting.) -/
theorem prime_rpow_le {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) {N p : ℕ} (hN : 8 ≤ N)
    (hN' : (2 : ℝ) ^ ((1 + ε) / ε) ≤ (N : ℝ)) (hp : p.Prime) (hpN : p ≤ N) :
    (N : ℝ) ≤ (p : ℝ) ^ ((1 + ε) * ((N / p : ℕ) : ℝ)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hkN : 0 < N / p := Nat.div_pos hpN hp0
  -- division bound: `N < (⌊N/p⌋ + 1) * p`
  have hNlt : N < (N / p + 1) * p := by
    rw [← Nat.div_lt_iff_lt_mul hp0]
    exact Nat.lt_succ_self _
  rcases Nat.lt_trichotomy (N / p) 2 with hlt | heq | hgt
  · -- Case `⌊N/p⌋ = 1`: `p > 2 ^ (1/ε)`, hence `N < 2p < p ^ (1+ε)`.
    have hk : N / p = 1 := by omega
    rw [hk]
    have hgoal : (1 + ε) * ((1 : ℕ) : ℝ) = 1 + ε := by push_cast; ring
    rw [hgoal]
    have hNlt2 : N < 2 * p := by
      have hh := hNlt
      rw [hk] at hh
      omega
    have hNlt2R : (N : ℝ) < 2 * (p : ℝ) := by exact_mod_cast hNlt2
    have hstep : (2 : ℝ) ^ ((1 + ε) / ε) = 2 * (2 : ℝ) ^ (1 / ε) := by
      have hdiv : (1 + ε) / ε = 1 + 1 / ε := by
        rw [add_div, div_self (ne_of_gt hε)]
        ring
      rw [hdiv, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    rw [hstep] at hN'
    have h2ε : (2 : ℝ) ^ (1 / ε) < (p : ℝ) := by linarith
    have hkey : (2 : ℝ) < (p : ℝ) ^ ε := by
      have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / ε) :=
        le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      have hlt' := Real.rpow_lt_rpow h0 h2ε hε
      have hval : ((2 : ℝ) ^ (1 / ε)) ^ ε = 2 := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div,
          inv_mul_cancel₀ (ne_of_gt hε), Real.rpow_one]
      linarith
    have hsplit : (p : ℝ) ^ (1 + ε) = (p : ℝ) ^ ε * (p : ℝ) := by
      rw [show (1 : ℝ) + ε = ε + 1 by ring, Real.rpow_add (by positivity), Real.rpow_one]
    have hfin : (N : ℝ) < (p : ℝ) ^ (1 + ε) :=
      calc (N : ℝ) < 2 * (p : ℝ) := hNlt2R
        _ < (p : ℝ) ^ ε * (p : ℝ) := mul_lt_mul_of_pos_right hkey (by positivity)
        _ = (p : ℝ) ^ (1 + ε) := hsplit.symm
    linarith
  · -- Case `⌊N/p⌋ = 2`: either `p = 2` (impossible as `N ≥ 8 > 3p`) or `3 ≤ p`.
    have hk : N / p = 2 := heq
    rw [hk]
    have hgoal : (1 + ε) * ((2 : ℕ) : ℝ) = (1 + ε) * 2 := by push_cast; ring
    rw [hgoal]
    have hNlt3 : N < 3 * p := by
      have hh := hNlt
      rw [hk] at hh
      omega
    by_cases hp3 : 3 ≤ p
    · have hpp : 3 * p ≤ p * p := by
        calc 3 * p = p * 3 := by ring
          _ ≤ p * p := Nat.mul_le_mul_left p hp3
      have hNpp : N < p * p := Nat.lt_of_lt_of_le hNlt3 hpp
      have hNppR : (N : ℝ) < (p : ℝ) ^ 2 := by
        have h1 : (N : ℝ) < ((p * p : ℕ) : ℝ) := by exact_mod_cast hNpp
        have h2 : ((p * p : ℕ) : ℝ) = (p : ℝ) ^ 2 := by push_cast; ring
        linarith
      have hexp : (2 : ℝ) ≤ (1 + ε) * 2 := by nlinarith [hε]
      have hmono : (p : ℝ) ^ (2 : ℝ) ≤ (p : ℝ) ^ ((1 + ε) * 2) :=
        Real.rpow_le_rpow_of_exponent_le hp1R hexp
      have hbridge : (p : ℝ) ^ 2 = (p : ℝ) ^ (2 : ℝ) :=
        (Real.rpow_natCast (p : ℝ) 2).symm
      exact le_of_lt (calc (N : ℝ) < (p : ℝ) ^ 2 := hNppR
        _ = (p : ℝ) ^ (2 : ℝ) := hbridge
        _ ≤ (p : ℝ) ^ ((1 + ε) * 2) := hmono)
    · have hp2' : p = 2 := by omega
      subst hp2'
      omega
  · -- Case `⌊N/p⌋ ≥ 3`: `N < (⌊N/p⌋+1) * p ≤ p ^ ⌊N/p⌋ ≤ p ^ ((1+ε) ⌊N/p⌋)`.
    have h1 : N / p + 1 ≤ 2 ^ (N / p - 1) := by
      have hbase := two_pow_add_two_le (N / p - 1) (by omega)
      omega
    have h2 : 2 ^ (N / p - 1) ≤ p ^ (N / p - 1) := Nat.pow_le_pow_left hp2 _
    have h3 : N < p ^ (N / p) := by
      have e1 : p * (N / p + 1) ≤ p * 2 ^ (N / p - 1) := Nat.mul_le_mul_left p h1
      have e2 : p * 2 ^ (N / p - 1) ≤ p * p ^ (N / p - 1) := Nat.mul_le_mul_left p h2
      have e3 : p * p ^ (N / p - 1) = p ^ (N / p) := by
        rw [mul_comm, ← Nat.pow_succ]
        congr 1
        omega
      calc N < (N / p + 1) * p := hNlt
        _ = p * (N / p + 1) := by ring
        _ ≤ p * 2 ^ (N / p - 1) := e1
        _ ≤ p * p ^ (N / p - 1) := e2
        _ = p ^ (N / p) := e3
    have hN3R : (N : ℝ) < ((p ^ (N / p) : ℕ) : ℝ) := by exact_mod_cast h3
    have hcast : ((p ^ (N / p) : ℕ) : ℝ) = (p : ℝ) ^ (((N / p : ℕ)) : ℝ) :=
      calc ((p ^ (N / p) : ℕ) : ℝ) = (p : ℝ) ^ (N / p) := Nat.cast_pow p (N / p)
        _ = (p : ℝ) ^ (((N / p : ℕ)) : ℝ) := (Real.rpow_natCast (p : ℝ) (N / p)).symm
    have hmono : (p : ℝ) ^ (((N / p : ℕ)) : ℝ)
        ≤ (p : ℝ) ^ ((1 + ε) * ((N / p : ℕ) : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hp1R ?_
      have hx : (0 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by positivity
      nlinarith [mul_nonneg (le_of_lt hε) hx]
    exact le_of_lt (calc (N : ℝ) < ((p ^ (N / p) : ℕ) : ℝ) := hN3R
      _ = (p : ℝ) ^ (((N / p : ℕ)) : ℝ) := hcast
      _ ≤ (p : ℝ) ^ ((1 + ε) * ((N / p : ℕ) : ℝ)) := hmono)

end Work.Analysis.IonescuWainger
