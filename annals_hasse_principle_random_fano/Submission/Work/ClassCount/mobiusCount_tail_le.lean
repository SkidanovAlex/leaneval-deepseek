import Mathlib
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.ClassCount.mobiusCount_le_box
import Submission.Work.ClassCount.harmonic_tail_inv_pow

namespace Work.ClassCount

open Finset

/-- **Tail bound for `mobiusCount`.**  For `n ≥ 1`, `0 < T₀`, `0 ≤ R` and `2 T₀ ≤ R`, the sum of
the `mobiusCount`s over `k ∈ Icc (⌊R/T₀⌋₊ + 1) ⌊R⌋₊` is at most `5^{n+1} 2^n R T₀^n / n`.

Route: `mobiusCount k ≤ #{z : Fin (n+1) → ℤ | eNorm z ≤ R/k} ≤ (2⌈R/k⌉₊+1)^{n+1}` (each coordinate
of `z` satisfies `|z i| ≤ eNorm z ≤ R/k`), and for `k ∈ Icc (⌊R/T₀⌋₊+1) ⌊R⌋₊` we have `k ≤ R` so
`1 ≤ R/k` and `2⌈R/k⌉₊+1 ≤ 5 R/k`; hence, with `K := ⌊R/T₀⌋₊` (and `K ≥ R/(2T₀) ≥ 1`, from
`T₀ > 0` and `2T₀ ≤ R`), the sum is at most `5^{n+1} R^{n+1} Σ_{k > K} k^{-(n+1)}` bounded by
`5^{n+1} R^{n+1} K^{-n}/n` (integral comparison for `x ↦ x^{-(n+1)}` at the lower limit `K`), and
`K^{-n} ≤ (2T₀/R)^n`. -/
theorem mobiusCount_tail_le (d n : ℕ) (hn : 1 ≤ n) (a : Work.HP.Mon d n → ℤ)
    (b : Fin (n + 1) → ℤ) (W : ℕ) (α R T₀ : ℝ)
    (hR : 0 ≤ R) (hT0 : 0 < T₀) (hT0R : 2 * T₀ ≤ R) :
    ∑ k ∈ Finset.Icc (⌊R / T₀⌋₊ + 1) ⌊R⌋₊, ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ)
      ≤ 5 ^ (n + 1) * (2 ^ n) * R * T₀ ^ n / n := by
  classical
  have hRpos : 0 < R := by linarith
  set K : ℕ := ⌊R / T₀⌋₊ with hKdef
  -- `K ≥ R/(2T₀)`, obtained as `2T₀·K > 2T₀(R/T₀ - 1) = 2R - 2T₀ ≥ R`.
  have hKgt : R / T₀ - 1 < (K : ℝ) := by
    have h := Nat.lt_floor_add_one (R / T₀)
    rw [hKdef]; linarith
  have hKge : R ≤ 2 * T₀ * (K : ℝ) := by
    have hmul : 2 * T₀ * (R / T₀ - 1) = 2 * R - 2 * T₀ := by field_simp
    have hlt : 2 * T₀ * (R / T₀ - 1) < 2 * T₀ * (K : ℝ) :=
      mul_lt_mul_of_pos_left hKgt (by linarith)
    rw [hmul] at hlt; linarith
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have h2 : (2 * T₀) * 0 < (2 * T₀) * (K : ℝ) := by
      have : (0 : ℝ) < 2 * T₀ * (K : ℝ) := by linarith
      linarith
    exact lt_of_mul_lt_mul_left h2 (le_of_lt (by linarith : (0 : ℝ) < 2 * T₀))
  have hK1 : 1 ≤ K := by
    have h2 : (2 * T₀) * 1 ≤ (2 * T₀) * (K : ℝ) := by linarith
    have : (1 : ℝ) ≤ (K : ℝ) := le_of_mul_le_mul_left h2 (by linarith : (0 : ℝ) < 2 * T₀)
    exact_mod_cast this
  -- `R/K ≤ 2T₀`
  have hRK : R / (K : ℝ) ≤ 2 * T₀ := by
    rw [div_le_iff₀ hKpos]; linarith
  -- per-term bound
  have hterm : ∀ k ∈ Finset.Icc (K + 1) ⌊R⌋₊,
      ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ)
        ≤ 5 ^ (n + 1) * (R / (k : ℝ)) ^ (n + 1) := by
    intro k hk
    obtain ⟨hk1', hk2'⟩ := Finset.mem_Icc.mp hk
    have hk1 : 1 ≤ k := by omega
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hkR : (k : ℝ) ≤ R := by
      have h2 : (k : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hk2'
      have h3 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR
      linarith
    have hx1 : (1 : ℝ) ≤ R / (k : ℝ) := by
      rw [le_div_iff₀ hkpos]; linarith
    have hceil : 2 * (⌈R / (k : ℝ)⌉₊ : ℝ) + 1 ≤ 5 * (R / (k : ℝ)) := by
      have hx0 : 0 < R / (k : ℝ) := lt_of_lt_of_le one_pos hx1
      have hc : ((⌈R / (k : ℝ)⌉₊ : ℕ) : ℝ) < R / (k : ℝ) + 1 :=
        Nat.ceil_lt_add_one (le_of_lt hx0)
      linarith
    calc ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ)
        ≤ (2 * (⌈R / (k : ℝ)⌉₊ : ℝ) + 1) ^ (n + 1) := mobiusCount_le_box d n a b W k α R
      _ ≤ (5 * (R / (k : ℝ))) ^ (n + 1) := pow_le_pow_left₀ (by positivity) hceil (n + 1)
      _ = 5 ^ (n + 1) * (R / (k : ℝ)) ^ (n + 1) := by rw [mul_pow]
  -- harmonic tail
  have htail : ∑ k ∈ Finset.Icc (K + 1) ⌊R⌋₊, (R / (k : ℝ)) ^ (n + 1)
      ≤ 2 ^ n * R * T₀ ^ n / n := by
    have hmain := harmonic_tail_inv_pow K ⌊R⌋₊ n hK1 hn
    have hA : R ^ (n + 1) * ((1 : ℝ) / (K : ℝ)) ^ n = R * (R / (K : ℝ)) ^ n := by
      rw [pow_succ, div_eq_mul_one_div, mul_pow]; ring
    calc ∑ k ∈ Finset.Icc (K + 1) ⌊R⌋₊, (R / (k : ℝ)) ^ (n + 1)
        = R ^ (n + 1) * ∑ k ∈ Finset.Icc (K + 1) ⌊R⌋₊, ((1 : ℝ) / (k : ℝ)) ^ (n + 1) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by rw [div_eq_mul_one_div, mul_pow])
      _ ≤ R ^ (n + 1) * ((1 / (K : ℝ)) ^ n / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = R * (R / (K : ℝ)) ^ n / n := by rw [← mul_div_assoc, hA]
      _ ≤ R * (2 * T₀) ^ n / n :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hRK n) (le_of_lt hRpos))
            (by positivity)
      _ = 2 ^ n * R * T₀ ^ n / n := by rw [mul_pow]; ring
  calc ∑ k ∈ Finset.Icc (K + 1) ⌊R⌋₊, ((Work.HP.mobiusCount d n a b W k α R : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Icc (K + 1) ⌊R⌋₊, 5 ^ (n + 1) * (R / (k : ℝ)) ^ (n + 1) :=
        Finset.sum_le_sum hterm
    _ = 5 ^ (n + 1) * ∑ k ∈ Finset.Icc (K + 1) ⌊R⌋₊, (R / (k : ℝ)) ^ (n + 1) := by
        rw [Finset.mul_sum]
    _ ≤ 5 ^ (n + 1) * (2 ^ n * R * T₀ ^ n / n) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 5 ^ (n + 1) * (2 ^ n) * R * T₀ ^ n / n := by ring

end Work.ClassCount
