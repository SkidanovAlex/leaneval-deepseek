import Mathlib

/-!
# Numerical slack absorption for `lem:second_squeeze` (Smith GON.tex)

After the squeeze/adjust/Remez steps one obtains a product lower bound

    exp((m+1)(n − m/2)·energy)·n^{−C0 n} ≤ p^{m+1} · ∏ᵢ ‖Qᵢ‖_n

where `p` (written `sqp0` below) is the common per-slot factor
`2 · m^{Cadj} · (2n)^{Crem} · ((k+1)(2m+1))`, while the goal is a bound with
the slightly weaker exponent `mn − m²/2` and a larger slack `n^{−Ctot·n}`.
This module supplies the pure real-arithmetic inequalities needed to absorb
`exp((n − m/2)·(−energy))·p^{m+1}` into `n^{(Ctot−C0)·n}`.

`e0 := −energy ≥ 0`.  The chosen final constant is

    sqC C0 Cadj Crem e0 = C0 + 2·Cadj + 4·Crem + 12 + e0 / log 2,

where `log 2 > 0`.  All inequalities hold for naturals `1 ≤ k ≤ m ≤ n`,
`2 ≤ n` and nonnegative reals `Cadj`, `Crem`, `e0`.

## Facts to prove
1. `sqp0_pos`: `0 < sqp0` (each factor is positive);
2. `sqp0_ge_one`: `1 ≤ sqp0`;
3. `log_sqp0_le`: `log p ≤ (Cadj + 2·Crem + 6)·log n`
   — write `log p = log 2 + Cadj·log m + Crem·log(2n) + log(k+1) + log(2m+1)`
   (`Real.log_mul`, `Real.log_rpow`) and bound each term by a multiple of
   `log n` using `Real.log_le_log` and `m ≤ n`, `k+1 ≤ 2n`, `2m+1 ≤ 3n`,
   `log 2 ≤ log n`, `log 3 ≤ 2·log n` for `n ≥ 2`;
4. `absorb`: the master inequality
   `(sqC C0 Cadj Crem e0 − C0)·n·log n ≥ (n − m/2)·e0 + (m+1)·log p`
   (use 3., `(m+1) ≤ 2n`, `(n − m/2) ≤ n`, `log n ≥ log 2 > 0` so
   `n·e0 ≤ n·log n·(e0/log 2)`).

Mathlib tools: `Real.log_mul`, `Real.log_rpow`, `Real.log_le_log`,
`Real.log_nonneg`, `Real.log_pos`, `Real.rpow_def_of_pos`,
`Real.rpow_pos_of_pos`, `Real.rpow_le_rpow`, `norm_num`, `nlinarith`,
`exact_mod_cast`.
-/

noncomputable section
open scoped BigOperators

namespace Submission.SlackAbsorb

/-- the common per-slot factor `2·m^{Cadj}·(2n)^{Crem}·(k+1)(2m+1)` -/
noncomputable def sqp0 (Cadj Crem : ℝ) (n m k : ℕ) : ℝ :=
  2 * (m : ℝ) ^ Cadj * (((2 * n : ℕ) : ℝ) ^ Crem) * (((k + 1) * (2 * m + 1) : ℕ) : ℝ)

/-- the final constant `C0 + 2Cadj + 4Crem + 12 + e0/log 2` -/
noncomputable def sqC (C0 Cadj Crem e0 : ℝ) : ℝ :=
  C0 + 2 * Cadj + 4 * Crem + 12 + e0 / Real.log 2

/-- positivity of the per-slot factor (holds without sign assumptions). -/
theorem sqp0_pos (Cadj Crem : ℝ) {n m k : ℕ} (hn2 : 2 ≤ n) (hm1 : 1 ≤ m) :
    0 < sqp0 Cadj Crem n m k := by
  unfold sqp0
  positivity

/-- the per-slot factor is at least one. -/
theorem sqp0_ge_one {Cadj Crem : ℝ} {n m k : ℕ} (hn2 : 2 ≤ n) (hm1 : 1 ≤ m)
    (hCadj : 0 ≤ Cadj) (hCrem : 0 ≤ Crem) :
    1 ≤ sqp0 Cadj Crem n m k := by
  unfold sqp0
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hf2 : (1 : ℝ) ≤ (m : ℝ) ^ Cadj := Real.one_le_rpow hm1R hCadj
  have h2n1 : (1 : ℝ) ≤ (((2 * n : ℕ) : ℝ)) := by
    have h : (2 : ℕ) ≤ 2 * n := by omega
    exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) h)
  have hf3 : (1 : ℝ) ≤ (((2 * n : ℕ) : ℝ) ^ Crem) := Real.one_le_rpow h2n1 hCrem
  have hf4 : (1 : ℝ) ≤ (((k + 1) * (2 * m + 1) : ℕ) : ℝ) := by
    have hc : (1 : ℕ) ≤ (k + 1) * (2 * m + 1) := by
      exact one_le_mul_of_one_le_of_one_le (by omega) (by omega)
    exact_mod_cast hc
  have h1 : (1 : ℝ) ≤ 2 * (m : ℝ) ^ Cadj := by
    exact one_le_mul_of_one_le_of_one_le (by norm_num) hf2
  have h2 : (1 : ℝ) ≤ 2 * (m : ℝ) ^ Cadj * (((2 * n : ℕ) : ℝ) ^ Crem) := by
    exact one_le_mul_of_one_le_of_one_le h1 hf3
  exact one_le_mul_of_one_le_of_one_le h2 hf4

/-- logarithm of the per-slot factor as a sum of logarithms. -/
lemma log_sqp0_eq (Cadj Crem : ℝ) {n m k : ℕ} (hn2 : 2 ≤ n) (hm1 : 1 ≤ m) :
    Real.log (sqp0 Cadj Crem n m k)
      = Real.log 2 + Cadj * Real.log (m : ℝ) + Crem * Real.log ((2 : ℝ) * (n : ℝ))
        + Real.log ((k : ℝ) + 1) + Real.log (2 * (m : ℝ) + 1) := by
  unfold sqp0
  push_cast
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2)
  have h2nR : (0 : ℝ) < (2 : ℝ) * (n : ℝ) := by nlinarith
  have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2m1R : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  rw [Real.log_mul (by positivity : (2 * (m : ℝ) ^ Cadj * ((2 : ℝ) * (n : ℝ)) ^ Crem) ≠ 0)
      (by positivity : (((k : ℝ) + 1) * (2 * (m : ℝ) + 1)) ≠ 0)]
  rw [Real.log_mul (by positivity : (2 * (m : ℝ) ^ Cadj) ≠ 0)
      (by positivity : ((2 : ℝ) * (n : ℝ)) ^ Crem ≠ 0)]
  rw [Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (by positivity : (m : ℝ) ^ Cadj ≠ 0)]
  rw [Real.log_mul (by positivity : ((k : ℝ) + 1) ≠ 0) (by positivity : (2 * (m : ℝ) + 1) ≠ 0)]
  rw [Real.log_rpow hmR Cadj]
  rw [Real.log_rpow h2nR Crem]
  ring

/-- log of the per-slot factor is O(log n). -/
theorem log_sqp0_le {n m k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hmn : m ≤ n)
    (hn2 : 2 ≤ n) {Cadj Crem : ℝ} (hCadj : 0 ≤ Cadj) (hCrem : 0 ≤ Crem) :
    Real.log (sqp0 Cadj Crem n m k) ≤ (Cadj + 2 * Crem + 6) * Real.log (n : ℝ) := by
  have hm1 : 1 ≤ m := le_trans hk1 hkm
  rw [log_sqp0_eq Cadj Crem hn2 hm1]
  have hmRpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hm1)
  have hnRpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2)
  let L : ℝ := Real.log (n : ℝ)
  have hLpos : 0 < L :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hn2))
  have hLnonneg : 0 ≤ L := le_of_lt hLpos
  -- log 2 ≤ log n
  have A1 : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num : (0 : ℝ) < (2 : ℝ)) (by exact_mod_cast hn2)
  -- log m ≤ log n  (m ≥ 1)
  have A2 : Real.log (m : ℝ) ≤ L := by
    dsimp [L]
    exact Real.log_le_log hmRpos (by exact_mod_cast hmn)
  have hCadjlog : Cadj * Real.log (m : ℝ) ≤ Cadj * L :=
    mul_le_mul_of_nonneg_left A2 hCadj
  -- log (2n) ≤ 2·log n
  have h2nlog : Real.log ((2 : ℝ) * (n : ℝ)) ≤ 2 * L := by
    dsimp [L]
    have heq : Real.log ((2 : ℝ) * (n : ℝ)) = Real.log 2 + Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hnRpos)]
    rw [heq]
    have hlg : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn2)
    nlinarith
  have hCremlog : Crem * Real.log ((2 : ℝ) * (n : ℝ)) ≤ Crem * (2 * L) :=
    mul_le_mul_of_nonneg_left h2nlog hCrem
  -- log (k+1) ≤ 2·log n   (k+1 ≤ 2n)
  have hk2n : (k : ℝ) + 1 ≤ (2 : ℝ) * (n : ℝ) := by
    exact_mod_cast (by omega : k + 1 ≤ 2 * n)
  have A4 : Real.log ((k : ℝ) + 1) ≤ 2 * L := by
    have hlt : Real.log ((k : ℝ) + 1) ≤ Real.log ((2 : ℝ) * (n : ℝ)) :=
      Real.log_le_log (by positivity : (0 : ℝ) < (k : ℝ) + 1) hk2n
    exact le_trans hlt h2nlog
  -- log (2m+1) ≤ 3·log n   (2m+1 ≤ 3n, log 3 ≤ 2·log n)
  have h2m3n : 2 * (m : ℝ) + 1 ≤ 3 * (n : ℝ) := by
    exact_mod_cast (by omega : 2 * m + 1 ≤ 3 * n)
  have hlog3le : Real.log 3 ≤ 2 * L := by
    dsimp [L]
    have hn3 : (3 : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith [show (2 : ℝ) ≤ (n : ℝ) from by exact_mod_cast hn2]
    have hle : Real.log (3 : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 3) hn3
    have hrw : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
      rw [pow_two, Real.log_mul (ne_of_gt hnRpos) (ne_of_gt hnRpos)]
      ring
    calc
      Real.log 3 ≤ Real.log ((n : ℝ) ^ 2) := hle
      _ = 2 * Real.log (n : ℝ) := hrw
  have A5 : Real.log (2 * (m : ℝ) + 1) ≤ 3 * L := by
    have hlt : Real.log (2 * (m : ℝ) + 1) ≤ Real.log (3 * (n : ℝ)) :=
      Real.log_le_log (by positivity : (0 : ℝ) < 2 * (m : ℝ) + 1) h2m3n
    have hlog3nle : Real.log (3 * (n : ℝ)) ≤ 3 * L := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hnRpos)]
      nlinarith [hlog3le, hLnonneg]
    exact le_trans hlt hlog3nle
  -- sum the five bounds
  have hsum : Real.log 2 + Cadj * Real.log (m : ℝ) + Crem * Real.log ((2 : ℝ) * (n : ℝ))
        + Real.log ((k : ℝ) + 1) + Real.log (2 * (m : ℝ) + 1)
      ≤ L + Cadj * L + Crem * (2 * L) + 2 * L + 3 * L := by
    nlinarith
  dsimp [L] at hsum
  nlinarith

/-- positivity of the final constant. -/
theorem sqC_pos {C0 Cadj Crem e0 : ℝ} (hC0 : 0 < C0) (hCadj : 0 ≤ Cadj)
    (hCrem : 0 ≤ Crem) (he0 : 0 ≤ e0) : 0 < sqC C0 Cadj Crem e0 := by
  unfold sqC
  have hg : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hdiv : 0 ≤ e0 / Real.log 2 := div_nonneg he0 (le_of_lt hg)
  nlinarith

/-- master slack-absorption inequality. -/
theorem absorb {n m k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m) (hmn : m ≤ n) (hn2 : 2 ≤ n)
    {C0 Cadj Crem e0 : ℝ} (hCadj : 0 ≤ Cadj) (hCrem : 0 ≤ Crem) (he0 : 0 ≤ e0) :
    (sqC C0 Cadj Crem e0 - C0) * (n : ℝ) * Real.log (n : ℝ) ≥
      ((n : ℝ) - (m : ℝ) / 2) * e0 + ((m + 1 : ℕ) : ℝ) * Real.log (sqp0 Cadj Crem n m k) := by
  have hm1 : 1 ≤ m := le_trans hk1 hkm
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hn2)
  have hmnonneg : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  have hnnonneg : 0 ≤ (n : ℝ) := le_of_lt hnR
  have hLpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hn2))
  have hLnonneg : 0 ≤ Real.log (n : ℝ) := le_of_lt hLpos
  have hg : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2le : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn2)
  have hp_le : Real.log (sqp0 Cadj Crem n m k) ≤
      (Cadj + 2 * Crem + 6) * Real.log (n : ℝ) :=
    log_sqp0_le hk1 hkm hmn hn2 hCadj hCrem
  have hB0 : 0 ≤ (Cadj + 2 * Crem + 6) * Real.log (n : ℝ) := by
    exact mul_nonneg (by nlinarith) hLnonneg
  have hm1nonneg : 0 ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (m + 1))
  have hstep1 : ((m + 1 : ℕ) : ℝ) * Real.log (sqp0 Cadj Crem n m k) ≤
      ((m + 1 : ℕ) : ℝ) * ((Cadj + 2 * Crem + 6) * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hp_le hm1nonneg
  have hm1le2n : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * (n : ℝ) := by
    exact_mod_cast (by omega : m + 1 ≤ 2 * n)
  have hstep2 : ((m + 1 : ℕ) : ℝ) * ((Cadj + 2 * Crem + 6) * Real.log (n : ℝ)) ≤
      ((2 : ℝ) * (n : ℝ)) * ((Cadj + 2 * Crem + 6) * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hm1le2n hB0
  have hstep3 : ((n : ℝ) - (m : ℝ) / 2) * e0 ≤ (n : ℝ) * e0 := by
    exact mul_le_mul_of_nonneg_right (by nlinarith) he0
  have hstep4 : (n : ℝ) * e0 ≤ (e0 / Real.log 2) * (n : ℝ) * Real.log (n : ℝ) := by
    have hdiv : 1 ≤ Real.log (n : ℝ) / Real.log 2 := (one_le_div hg).2 hlog2le
    have hne : 0 ≤ (n : ℝ) * e0 := mul_nonneg hnnonneg he0
    calc
      (n : ℝ) * e0 = ((n : ℝ) * e0) * 1 := by ring
      _ ≤ ((n : ℝ) * e0) * (Real.log (n : ℝ) / Real.log 2) := by
        exact mul_le_mul_of_nonneg_left hdiv hne
      _ = (e0 / Real.log 2) * (n : ℝ) * Real.log (n : ℝ) := by ring
  calc
    ((n : ℝ) - (m : ℝ) / 2) * e0 + ((m + 1 : ℕ) : ℝ) * Real.log (sqp0 Cadj Crem n m k)
        ≤ (n : ℝ) * e0 + ((m + 1 : ℕ) : ℝ) * Real.log (sqp0 Cadj Crem n m k) := by
          nlinarith [hstep3]
    _ ≤ (n : ℝ) * e0 + ((m + 1 : ℕ) : ℝ) * ((Cadj + 2 * Crem + 6) * Real.log (n : ℝ)) := by
          nlinarith [hstep1]
    _ ≤ (n : ℝ) * e0 + ((2 : ℝ) * (n : ℝ)) * ((Cadj + 2 * Crem + 6) * Real.log (n : ℝ)) := by
          nlinarith [hstep2]
    _ = (n : ℝ) * e0 + (2 * Cadj + 4 * Crem + 12) * (n : ℝ) * Real.log (n : ℝ) := by
          ring
    _ ≤ (e0 / Real.log 2) * (n : ℝ) * Real.log (n : ℝ)
          + (2 * Cadj + 4 * Crem + 12) * (n : ℝ) * Real.log (n : ℝ) := by
          nlinarith [hstep4]
    _ = (sqC C0 Cadj Crem e0 - C0) * (n : ℝ) * Real.log (n : ℝ) := by
          unfold sqC
          ring

end Submission.SlackAbsorb
