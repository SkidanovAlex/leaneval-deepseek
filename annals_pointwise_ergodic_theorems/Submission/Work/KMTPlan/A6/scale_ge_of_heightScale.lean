import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs

namespace Work.KMTPlan.A6

/-- **The height scale determines the size of `N`.**

If `L` lies in the window `[2 C₀, heightScale C₀ N] = [2 C₀, C₀ · LogLog N]`, then `N` is at
least `2^(2^(L/C₀ - 2))`.  Equivalently: the height scale `l_{(N)} = C₀ LogLog N` is at most
`C₀ (2 + log₂ log₂ N)`, i.e. `2^(l/C₀ - 2) ≤ log₂ N` for every admissible `l ≤ l_{(N)}`.

The proof is the elementary chain

`2^(L/C₀ - 2) ≤ 2^(m - 2) ≤ (k+2)/4 ≤ k ≤ log₂ N`, with `k = log₂(max N 2)`, `m = log₂(k+2)`,

using `2^k ≤ max N 2` and `2^m ≤ k + 2`.  The hypothesis `2 C₀ ≤ L` is used twice: it gives
`2 ≤ m` (hence `k ≥ 2`, hence `max N 2 = N`), and it makes the exponent `L/C₀ - 2` nonnegative. -/
theorem scale_ge_of_heightScale (C₀ : ℕ) (hC₀ : 1 ≤ C₀) {N L : ℕ} (hN : 1 ≤ N)
    (h : L ≤ Work.Analysis.EndVar.heightScale C₀ N) (hL : 2 * C₀ ≤ L) :
    (2 : ℝ) ^ ((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) ≤ (N : ℝ) := by
  have hC₀pos_nat : 0 < C₀ := by omega
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast hC₀pos_nat
  set k : ℕ := Nat.log 2 (max N 2) with hk
  set m : ℕ := Nat.log 2 (k + 2) with hm
  have hlogLog : Work.Analysis.EndVar.logLogN N = m := by
    simp only [Work.Analysis.EndVar.logLogN]
    rw [← hk, ← hm]
  have hle : L ≤ C₀ * m := by
    rw [Work.Analysis.EndVar.heightScale, hlogLog] at h
    exact h
  -- `2 ≤ m`, from `2 C₀ ≤ L ≤ C₀ m`
  have hm2 : 2 ≤ m := by
    have h1 : C₀ * 2 ≤ C₀ * m := by
      calc C₀ * 2 = 2 * C₀ := by ring
        _ ≤ L := hL
        _ ≤ C₀ * m := hle
    exact Nat.le_of_mul_le_mul_left h1 hC₀pos_nat
  -- hence `k ≥ 2`, so `max N 2 = N` and `2^k ≤ N`
  have hk2 : 2 ≤ k := by
    have h2m : 2 ^ m ≤ k + 2 := Nat.pow_log_le_self 2 (by omega)
    have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have h42 : 4 ≤ k + 2 := le_trans (by simpa using h4) h2m
    omega
  have hkN : 2 ^ k ≤ max N 2 := Nat.pow_log_le_self 2 (by positivity)
  have h4k : 4 ≤ 2 ^ k := by simpa using (Nat.pow_le_pow_right (by norm_num : 0 < 2) hk2)
  have h4max : 4 ≤ max N 2 := le_trans h4k hkN
  have hN2 : 2 ≤ N := by
    rcases lt_or_ge N 2 with h2 | h2
    · rw [max_eq_right (le_of_lt h2)] at h4max
      omega
    · exact h2
  have h2kN : 2 ^ k ≤ N := by rwa [max_eq_left hN2] at hkN
  -- the real exponent comparison
  have hLC : (L : ℝ) ≤ (C₀ : ℝ) * (m : ℝ) := by exact_mod_cast hle
  have hA_le : (L : ℝ) / (C₀ : ℝ) - 2 ≤ (m : ℝ) - 2 := by
    have hdiv : (L : ℝ) / (C₀ : ℝ) ≤ (m : ℝ) :=
      (div_le_iff₀ hC₀pos).mpr (by linarith)
    linarith
  have hrpow_le : (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ) - 2) ≤ (k : ℝ) := by
    have h1 : (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ) - 2) ≤ (2:ℝ) ^ ((m:ℝ) - 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hA_le
    have hsub : (2:ℝ) ^ ((m:ℝ) - 2) = (2:ℝ) ^ (m:ℝ) / 4 := by
      rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
      norm_num
    have h2m : (2:ℝ) ^ (m:ℝ) ≤ (k : ℝ) + 2 := by
      have h : (2 ^ m : ℕ) ≤ k + 2 := Nat.pow_log_le_self 2 (by omega)
      have h' : ((2 ^ m : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      rw [Real.rpow_natCast]
      exact h'
    have h4 : ((k : ℝ) + 2) / 4 ≤ (k : ℝ) := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      linarith
    linarith
  have h2k_le_N : (2:ℝ) ^ (k:ℝ) ≤ (N:ℝ) := by
    have h : ((2 ^ k : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast h2kN
    push_cast at h
    rw [Real.rpow_natCast]
    exact h
  have h2rpow : (2:ℝ) ^ ((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ) - 2)) ≤ (2:ℝ) ^ (k:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hrpow_le
  linarith

end Work.KMTPlan.A6
