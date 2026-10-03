/-
  Companion paper (§5), part 2: the weighted prime sum and the evaluation of `T(x;y,z)`.

  This file contains:
  * `psum_bound` : the weighted prime sum `∑_{p ≤ P} (log p) g(p/(ν,p))² (log max 2 (⌊M/p⌋/(2ν)))^{-6}`
    is `≪ (log M)^{-6}(1 + log ν)` in the range `ν⁴ ≤ M`;
  * (to follow) `abs_Tnu_le`, the remainder bound, and `Tsum2_eval`.
-/
import Mathlib
import Submission.ASP.Defs
import Submission.Work.FIChain.LocalS4
import Submission.Work.FIChain.LocalS5
import Submission.Work.FIChain.LocalS5b
import Submission.Commons.NumberTheory.Sieve.sum_primes_log_div_sq_le
import Submission.Commons.NumberTheory.Sieve.sum_primes_log_div_sq_tail_le
import Submission.Commons.NumberTheory.Nat.sum_log_primeFactors_le_log

namespace Submission.ASP

open Finset

noncomputable section

/-! ### Elementary arithmetic helpers -/

/-- `gcd ν p = 1` for a prime `p` not dividing `ν`. -/
private lemma gcd_eq_one_of_not_dvd {ν p : ℕ} (hp : p.Prime) (h : ¬ p ∣ ν) :
    Nat.gcd ν p = 1 := by
  rcases hp.eq_one_or_self_of_dvd (Nat.gcd ν p) (Nat.gcd_dvd_right ν p) with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ Nat.gcd_dvd_left ν p) h

/-- `gcd ν p = p` when `p ∣ ν`. -/
private lemma gcd_eq_self_of_dvd {ν p : ℕ} (h : p ∣ ν) : Nat.gcd ν p = p :=
  Nat.gcd_eq_right h

/-- `4ν³ ≤ M` when `ν ≥ 1`, `ν⁴ ≤ M` and `M ≥ 256`. -/
private lemma four_mul_cube_le_of_pow_four_le {ν M : ℕ} (hν1 : 1 ≤ ν) (hν4 : ν ^ 4 ≤ M)
    (hM : 256 ≤ M) : 4 * ν ^ 3 ≤ M := by
  rcases Nat.lt_or_ge ν 4 with h3 | h3
  · have h1 : ν ^ 3 ≤ 27 := by
      have := Nat.pow_le_pow_left (by omega : ν ≤ 3) 3
      simpa using this
    omega
  · have h4 : 4 ≤ ν := h3
    have h5 : 4 * ν ^ 3 ≤ ν * ν ^ 3 := Nat.mul_le_mul_right (ν ^ 3) h4
    have h6 : ν * ν ^ 3 = ν ^ 4 := by ring
    rw [h6] at h5
    exact le_trans h5 hν4

/-- If `M < 4νp²`, `ν⁴ ≤ M` and `M ≥ 256` then `p ∤ ν`. -/
private lemma not_dvd_of_four_mul_sq_gt {ν M p : ℕ} (hν1 : 1 ≤ ν) (hν4 : ν ^ 4 ≤ M)
    (hM : 256 ≤ M) (h : M < 4 * ν * p ^ 2) : ¬ p ∣ ν := by
  intro hd
  have hνpos : 0 < ν := by omega
  have hpν : p ≤ ν := Nat.le_of_dvd hνpos hd
  have hcube : 4 * ν ^ 3 ≤ M := four_mul_cube_le_of_pow_four_le hν1 hν4 hM
  have hp2 : p ^ 2 ≤ ν ^ 2 := Nat.pow_le_pow_left hpν 2
  have hle : 4 * ν * p ^ 2 ≤ 4 * ν * ν ^ 2 := Nat.mul_le_mul_left (4 * ν) hp2
  have heq : 4 * ν * ν ^ 2 = 4 * ν ^ 3 := by ring
  rw [heq] at hle
  omega

/-- Auxiliary: `x^{-6} ≤ 8^6 L^{-6}` when `L/8 ≤ x` and `0 < L`. -/
private lemma zpow_neg_six_le {x L : ℝ} (hx : L / 8 ≤ x) (hL : 0 < L) :
    x ^ (-(6 : ℤ)) ≤ 8 ^ 6 * L ^ (-(6 : ℤ)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by linarith) hx
  have h6 : (L / 8) ^ 6 ≤ x ^ 6 := pow_le_pow_left₀ (by linarith) hx 6
  have h8 : (L / 8) ^ 6 = L ^ 6 / 8 ^ 6 := by rw [div_pow]
  rw [h8] at h6
  simp only [zpow_neg, zpow_natCast]
  have hstep1 : (x ^ 6)⁻¹ ≤ (L ^ 6 / 8 ^ 6)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr h6
  have hstep2 : (L ^ 6 / 8 ^ 6)⁻¹ = 8 ^ 6 * (L ^ 6)⁻¹ := by
    rw [inv_div, div_eq_mul_inv]
  calc (x ^ 6)⁻¹ ≤ (L ^ 6 / 8 ^ 6)⁻¹ := hstep1
    _ = 8 ^ 6 * (L ^ 6)⁻¹ := hstep2

/-- Auxiliary: `8 log 2 ≤ log M` for `M ≥ 256`. -/
private lemma eight_log_two_le' {M : ℕ} (hM : 256 ≤ M) :
    8 * Real.log 2 ≤ Real.log (M : ℝ) := by
  have h1 : (256 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h2 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    have h3 := Real.log_pow (2 : ℝ) 8
    norm_num at h3
    linarith [h3]
  linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 256) h1, h2]

/-- **Region 1 of the weighted prime sum**: if `4νp² ≤ M`, `ν ≥ 1`, `p ≥ 2` and `M ≥ 256`,
then `log (max 2 (⌊M/p⌋/(2ν))) ≥ (1/8) log M`. -/
private lemma region1_log {ν M p : ℕ} (hν1 : 1 ≤ ν) (hν4 : ν ^ 4 ≤ M) (hp2 : 2 ≤ p)
    (hM : 256 ≤ M) (h : 4 * ν * p ^ 2 ≤ M) :
    (Real.log (M : ℝ)) / 8 ≤ Real.log (max 2 (((M / p : ℕ) : ℝ) / (2 * (ν : ℝ)))) := by
  have hp0 : 0 < p := by omega
  have hν0 : 0 < ν := by omega
  have h4p : 4 * p ≤ M := by
    have h1 : 4 * p ≤ 4 * ν * p ^ 2 := by nlinarith [hν1, hp2]
    linarith [h1, h]
  have hMp1 : 1 ≤ M / p := (Nat.one_le_div_iff hp0).mpr (by omega)
  have hkey : M ≤ 2 * p * (M / p) := by
    have hlt : M < (M / p + 1) * p := (Nat.div_lt_iff_lt_mul hp0).mp (Nat.lt_succ_self _)
    have h1 : (M / p + 1) * p = p * (M / p) + p := by ring
    have h2 : p * (M / p) + p ≤ 2 * p * (M / p) := by
      have h3 : p * 1 ≤ p * (M / p) := Nat.mul_le_mul_left p hMp1
      nlinarith [h3]
    omega
  have hkeyR : (M : ℝ) ≤ 2 * (p : ℝ) * ((M / p : ℕ) : ℝ) := by exact_mod_cast hkey
  have hq : (M : ℝ) / (2 * (p : ℝ)) ≤ ((M / p : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hkeyR]
  set q : ℝ := ((M / p : ℕ) : ℝ) / (2 * (ν : ℝ)) with hqdef
  have hq_ge : (M : ℝ) / (4 * (ν : ℝ) * (p : ℝ)) ≤ q := by
    rw [hqdef]
    have hstep : (M : ℝ) / (2 * (p : ℝ)) / (2 * (ν : ℝ)) ≤
        ((M / p : ℕ) : ℝ) / (2 * (ν : ℝ)) :=
      div_le_div_of_nonneg_right hq (by positivity)
    have heq : (M : ℝ) / (2 * (p : ℝ)) / (2 * (ν : ℝ)) =
        (M : ℝ) / (4 * (ν : ℝ) * (p : ℝ)) := by
      rw [div_div]
      congr 1
      ring
    rwa [heq] at hstep
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hq_pos : 0 < q := lt_of_lt_of_le (div_pos hMpos (by positivity)) hq_ge
  have hnat : 16 * ν ^ 4 * p ^ 4 ≤ M ^ 3 := by
    have hA : (4 * ν * p ^ 2) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left h 2
    have hB : ν ^ 2 ≤ M := by nlinarith [hν1, hν4]
    have e : (4 * ν * p ^ 2) ^ 2 * ν ^ 2 = 16 * ν ^ 4 * p ^ 4 := by ring
    calc 16 * ν ^ 4 * p ^ 4 = (4 * ν * p ^ 2) ^ 2 * ν ^ 2 := e.symm
      _ ≤ M ^ 2 * M := Nat.mul_le_mul hA hB
      _ = M ^ 3 := by ring
  have hR : 16 * (ν : ℝ) ^ 4 * (p : ℝ) ^ 4 ≤ (M : ℝ) ^ 3 := by exact_mod_cast hnat
  have hq4 : (M : ℝ) / 16 ≤ q ^ 4 := by
    have h2 : ((M : ℝ) / (4 * (ν : ℝ) * (p : ℝ))) ^ 4 ≤ q ^ 4 :=
      pow_le_pow_left₀ (by positivity) hq_ge 4
    have h3 : ((M : ℝ) / (4 * (ν : ℝ) * (p : ℝ))) ^ 4 =
        (M : ℝ) ^ 4 / (256 * (ν : ℝ) ^ 4 * (p : ℝ) ^ 4) := by
      rw [div_pow]
      ring
    have h4 : (M : ℝ) / 16 ≤ (M : ℝ) ^ 4 / (256 * (ν : ℝ) ^ 4 * (p : ℝ) ^ 4) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [hR, hMpos]
    linarith [h2, h3 ▸ h4]
  have hq_ge_root : ((M : ℝ) / 16) ^ ((4 : ℝ)⁻¹) ≤ q := by
    have hpow : (((M : ℝ) / 16) ^ ((4 : ℝ)⁻¹)) ^ (4 : ℕ) = (M : ℝ) / 16 :=
      Real.rpow_inv_natCast_pow (by positivity) (by norm_num)
    have h1 : (((M : ℝ) / 16) ^ ((4 : ℝ)⁻¹)) ^ (4 : ℕ) ≤ q ^ 4 := by
      rw [hpow]; exact hq4
    exact (pow_le_pow_iff_left₀ (by positivity) hq_pos.le (by norm_num)).mp h1
  have hq2 : 2 ≤ q := by
    have h16b : (2 : ℝ) ^ 4 ≤ (M : ℝ) / 16 := by
      have h1 : (256 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      norm_num
      linarith
    have h1 : (2 : ℝ) ^ 4 ≤ q ^ 4 := le_trans h16b hq4
    exact (pow_le_pow_iff_left₀ (by norm_num) hq_pos.le (by norm_num)).mp h1
  rw [max_eq_right hq2, hqdef]
  have hlogq : (1 / 4) * Real.log ((M : ℝ) / 16) ≤ Real.log q := by
    have h1 := Real.log_le_log (by positivity : (0 : ℝ) < ((M : ℝ) / 16) ^ ((4 : ℝ)⁻¹))
      hq_ge_root
    rw [Real.log_rpow (by positivity)] at h1
    simpa only [one_div] using h1
  have hlog16 : Real.log ((M : ℝ) / 16) = Real.log (M : ℝ) - Real.log 16 :=
    Real.log_div (by positivity) (by norm_num)
  have hlog16' : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h3 := Real.log_pow (2 : ℝ) 4
    norm_num at h3
    linarith [h3]
  have h8log2 : 8 * Real.log 2 ≤ Real.log (M : ℝ) := eight_log_two_le' hM
  have h2 : (1 / 4) * Real.log ((M : ℝ) / 16) =
      (1 / 4) * Real.log (M : ℝ) - Real.log 2 := by
    rw [hlog16, hlog16']
    ring
  rw [h2] at hlogq
  linarith

/-- **Region 2 of the weighted prime sum**: if `M < 4νp²`, `ν⁴ ≤ M` and `M ≥ 256`, then
`(log M)^{12}/4 < p`. -/
private lemma region2_log_lt {ν M p : ℕ} (hν1 : 1 ≤ ν) (hν4 : ν ^ 4 ≤ M) (hM : 256 ≤ M)
    (hlog : (Real.log (M : ℝ)) ^ 6 ≤ (M : ℝ) ^ ((3 : ℝ) / 16))
    (h : M < 4 * ν * p ^ 2) :
    (Real.log (M : ℝ)) ^ 12 / 4 < (p : ℝ) := by
  have hν0 : 0 < ν := by omega
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp; simp at h
    · exact hp
  have hν3 : ν ^ 3 < 4 * p ^ 2 := by
    have e1 : ν ^ 4 = ν * ν ^ 3 := by ring
    have e2 : 4 * ν * p ^ 2 = ν * (4 * p ^ 2) := by ring
    have hlt : ν * ν ^ 3 < ν * (4 * p ^ 2) := by
      rw [← e1, ← e2]; exact lt_of_le_of_lt hν4 h
    exact (Nat.mul_lt_mul_left hν0).mp hlt
  have hM3 : M ^ 3 < 256 * p ^ 8 := by
    have h1 : M ^ 3 < (4 * ν * p ^ 2) ^ 3 := Nat.pow_lt_pow_left h (by norm_num)
    rw [show (4 * ν * p ^ 2) ^ 3 = 64 * ν ^ 3 * p ^ 6 from by ring] at h1
    have h2 : 64 * ν ^ 3 * p ^ 6 < 256 * p ^ 8 := by
      have hpos : 0 < 64 * p ^ 6 := by positivity
      have h3 := Nat.mul_lt_mul_of_pos_left hν3 hpos
      have e : 64 * ν ^ 3 * p ^ 6 = (64 * p ^ 6) * ν ^ 3 := by ring
      have e' : 256 * p ^ 8 = (64 * p ^ 6) * (4 * p ^ 2) := by ring
      rw [e, e']
      exact h3
    exact lt_trans h1 h2
  have hM3R : (M : ℝ) ^ 3 < 256 * (p : ℝ) ^ 8 := by exact_mod_cast hM3
  have hp8 : (M : ℝ) ^ 3 / 256 < (p : ℝ) ^ 8 := by
    rw [div_lt_iff₀ (by norm_num)]
    linarith [hM3R]
  have hMpow : ((M : ℝ) ^ ((3 : ℝ) / 8) / 4) ^ 8 = (M : ℝ) ^ 3 / 65536 := by
    rw [div_pow]
    have h1 : ((M : ℝ) ^ ((3 : ℝ) / 8)) ^ (8 : ℕ) = (M : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast ((M : ℝ) ^ ((3 : ℝ) / 8)) 8,
        ← Real.rpow_mul (show (0 : ℝ) ≤ (M : ℝ) by positivity)]
      norm_num
    rw [h1]
    norm_num
  have hlt8 : ((M : ℝ) ^ ((3 : ℝ) / 8) / 4) ^ 8 < (p : ℝ) ^ 8 := by
    rw [hMpow]
    have hM3pos : (0 : ℝ) < (M : ℝ) ^ 3 := by positivity
    have h1 : (M : ℝ) ^ 3 / 65536 < (M : ℝ) ^ 3 / 256 :=
      div_lt_div_of_pos_left hM3pos (by norm_num) (by norm_num)
    linarith [h1, hp8]
  have hmain : (M : ℝ) ^ ((3 : ℝ) / 8) / 4 < (p : ℝ) :=
    (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hlt8
  have hlog12 : (Real.log (M : ℝ)) ^ 12 ≤ (M : ℝ) ^ ((3 : ℝ) / 8) := by
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (Real.log (M : ℝ)) ^ 6) hlog 2
    have e : ((Real.log (M : ℝ)) ^ 6) ^ 2 = (Real.log (M : ℝ)) ^ 12 := by ring
    have e2 : ((M : ℝ) ^ ((3 : ℝ) / 16)) ^ 2 = (M : ℝ) ^ ((3 : ℝ) / 8) := by
      rw [← Real.rpow_natCast ((M : ℝ) ^ ((3 : ℝ) / 16)) 2,
        ← Real.rpow_mul (show (0 : ℝ) ≤ (M : ℝ) by positivity)]
      norm_num
    rwa [e, e2] at hsq
  linarith

/-- Auxiliary: `(log 2)^{-6} ≤ 10`. -/
private lemma log_two_zpow_le' : (Real.log 2) ^ (-(6 : ℤ)) ≤ 10 := by
  have h1 : (0.69 : ℝ) ≤ Real.log 2 := le_of_lt (by linarith [Real.log_two_gt_d9])
  have h5 : (1 : ℝ) ≤ 10 * (Real.log 2) ^ 6 := by
    have h3 : (0.1 : ℝ) ≤ (0.69 : ℝ) ^ (6 : ℕ) := by norm_num
    have h4 : (0.69 : ℝ) ^ 6 ≤ (Real.log 2) ^ 6 := pow_le_pow_left₀ (by norm_num) h1 6
    nlinarith
  have h7 : ((Real.log 2) ^ 6)⁻¹ ≤ 10 :=
    (inv_le_iff_one_le_mul₀ (by positivity : (0 : ℝ) < (Real.log 2) ^ 6)).mpr h5
  calc (Real.log 2) ^ (-(6 : ℤ)) = ((Real.log 2) ^ 6)⁻¹ := by simp [zpow_neg]
    _ ≤ 10 := h7

/-- Auxiliary: `x^{-6} ≤ 10` when `log 2 ≤ x`. -/
private lemma zpow_neg_six_le_log_two {x : ℝ} (hx : Real.log 2 ≤ x) :
    x ^ (-(6 : ℤ)) ≤ 10 := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num)) hx
  have h6 : (Real.log 2) ^ 6 ≤ x ^ 6 :=
    pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) hx 6
  calc x ^ (-(6 : ℤ)) = ((x ^ 6)⁻¹) := by simp [zpow_neg]
    _ ≤ (((Real.log 2) ^ 6)⁻¹) := (inv_le_inv₀ (pow_pos hx0 6) (by positivity)).mpr h6
    _ = (Real.log 2) ^ (-(6 : ℤ)) := by simp [zpow_neg]
    _ ≤ 10 := log_two_zpow_le'

/-- The weighted prime sum of §5 of the companion paper. -/
lemma psum_bound {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hg0 : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν M P : ℕ, 1 ≤ ν → ν ^ 4 ≤ M → 256 ≤ M →
      (Real.log (M : ℝ)) ^ 6 ≤ (M : ℝ) ^ ((3 : ℝ) / 16) →
      (∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
        Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2
          * (Real.log (max 2 (((M / p : ℕ) : ℝ) / (2 * (ν : ℝ))))) ^ (-(6 : ℤ)))
      ≤ C * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (1 + Real.log (ν : ℝ)) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := hbound
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.NumberTheory.Sieve.sum_primes_log_div_sq_le
  obtain ⟨C2, hC2pos, hC2⟩ := Commons.NumberTheory.Sieve.sum_primes_log_div_sq_tail_le
  set Cm : ℝ := max Cg 1 with hCm
  have hCm1 : 1 ≤ Cm := le_max_right _ _
  have hCmg : Cg ≤ Cm := le_max_left _ _
  have hCmpos : 0 < Cm := lt_of_lt_of_le one_pos hCm1
  refine ⟨8 ^ 6 * (Cm ^ 2 * C1 + 1) + 20 * Cm ^ 2 * C2, by positivity, ?_⟩
  intro ν M P hν1 hν4 hM hlog
  set Ps : Finset ℕ := (Finset.Icc 1 P).filter Nat.Prime with hPs
  set ξ : ℕ → ℝ := fun p => Real.log (max 2 (((M / p : ℕ) : ℝ) / (2 * (ν : ℝ)))) with hξ
  have hLpos : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlogν0 : 0 ≤ Real.log (ν : ℝ) := Real.log_nonneg (by exact_mod_cast hν1)
  have hξlog2 : ∀ p, Real.log 2 ≤ ξ p := by
    intro p
    rw [hξ]
    exact Real.log_le_log (by norm_num) (le_max_left _ _)
  have hξ10 : ∀ p, (ξ p) ^ (-(6 : ℤ)) ≤ 10 := fun p => zpow_neg_six_le_log_two (hξlog2 p)
  have hξ0 : ∀ p, 0 ≤ (ξ p) ^ (-(6 : ℤ)) := fun p =>
    le_of_lt (zpow_pos (lt_of_lt_of_le (Real.log_pos (by norm_num)) (hξlog2 p)) _)
  have hg_le : ∀ p : ℕ, p.Prime → g p ≤ Cm / (p : ℝ) := by
    intro p hp
    calc g p ≤ Cg / (p : ℝ) := hCg p hp
      _ ≤ Cm / (p : ℝ) := div_le_div_of_nonneg_right hCmg (by positivity)
  have hg_sq : ∀ p : ℕ, p.Prime → (g (p / Nat.gcd ν p)) ^ 2
      ≤ (Cm / (p : ℝ)) ^ 2 + (if p ∣ ν then 1 else 0) := by
    intro p hp
    by_cases hd : p ∣ ν
    · rw [if_pos hd, gcd_eq_self_of_dvd hd, Nat.div_self hp.pos, hg1]
      norm_num
      linarith [sq_nonneg (Cm / (p : ℝ))]
    · rw [if_neg hd, gcd_eq_one_of_not_dvd hp hd, Nat.div_one]
      have h1 := pow_le_pow_left₀ (hg0 p hp) (hg_le p hp) 2
      linarith [sq_nonneg (Cm / (p : ℝ))]
  -- bound `∑_p log p g_p²` over the whole prime set
  have hsumg : (∑ p ∈ Ps, Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2)
      ≤ Cm ^ 2 * C1 + Real.log (ν : ℝ) := by
    have hpt : ∀ p ∈ Ps, Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2
        ≤ Cm ^ 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2)
          + (if p ∣ ν then Real.log (p : ℝ) else 0) := by
      intro p hp
      rw [hPs, Finset.mem_filter] at hp
      obtain ⟨hpIcc, hpprime⟩ := hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hpIcc).1
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
      have h2 := hg_sq p hpprime
      have h3 : Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2
          ≤ Real.log (p : ℝ) * ((Cm / (p : ℝ)) ^ 2 + (if p ∣ ν then 1 else 0)) :=
        mul_le_mul_of_nonneg_left h2 hlogp
      have h6 : Real.log (p : ℝ) * (Cm / (p : ℝ)) ^ 2
          = Cm ^ 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
        field_simp
      by_cases hd : p ∣ ν
      · rw [if_pos hd] at h3 ⊢
        have : Real.log (p : ℝ) * ((Cm / (p : ℝ)) ^ 2 + 1)
            = Real.log (p : ℝ) * (Cm / (p : ℝ)) ^ 2 + Real.log (p : ℝ) := by ring
        rw [this] at h3
        linarith [mul_nonneg hlogp (sq_nonneg (Cm / (p : ℝ)))]
      · rw [if_neg hd] at h3 ⊢
        linarith [mul_nonneg hlogp (sq_nonneg (Cm / (p : ℝ)))]
    calc (∑ p ∈ Ps, Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2)
        ≤ ∑ p ∈ Ps, (Cm ^ 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2)
            + (if p ∣ ν then Real.log (p : ℝ) else 0)) := Finset.sum_le_sum hpt
      _ = Cm ^ 2 * (∑ p ∈ Ps, Real.log (p : ℝ) / (p : ℝ) ^ 2)
            + ∑ p ∈ Ps, (if p ∣ ν then Real.log (p : ℝ) else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ Cm ^ 2 * C1 + Real.log (ν : ℝ) := by
          have hA : (∑ p ∈ Ps, Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤ C1 := by
            rw [hPs]; exact hC1 P
          have hB : (∑ p ∈ Ps, (if p ∣ ν then Real.log (p : ℝ) else 0)) ≤ Real.log (ν : ℝ) := by
            rw [← Finset.sum_filter]
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
              (Commons.NumberTheory.Nat.sum_log_primeFactors_le_log ν)
            · intro p hp
              rw [Finset.mem_filter] at hp
              obtain ⟨hpPs, hpdvd⟩ := hp
              rw [hPs, Finset.mem_filter] at hpPs
              exact Nat.mem_primeFactors.mpr ⟨hpPs.2, hpdvd, by omega⟩
            · intro p hp _
              rw [Nat.mem_primeFactors] at hp
              exact Real.log_nonneg (by exact_mod_cast hp.1.one_le)
          have hCm2 : (0 : ℝ) ≤ Cm ^ 2 := sq_nonneg _
          nlinarith [hA, hB, hCm2]
  -- region 1
  have hreg1 : (∑ p ∈ Ps.filter (fun p => 4 * ν * p ^ 2 ≤ M),
      Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * (ξ p) ^ (-(6 : ℤ)))
      ≤ 8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (Cm ^ 2 * C1 + 1)
          * (1 + Real.log (ν : ℝ)) := by
    have hpt : ∀ p ∈ Ps.filter (fun p => 4 * ν * p ^ 2 ≤ M),
        Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * (ξ p) ^ (-(6 : ℤ))
        ≤ 8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
            * (Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpPs, hp4⟩ := hp
      rw [hPs, Finset.mem_filter] at hpPs
      obtain ⟨hpIcc, hpprime⟩ := hpPs
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hpIcc).1
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
      have h1 : (ξ p) ^ (-(6 : ℤ)) ≤ 8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) :=
        zpow_neg_six_le (by simpa [hξ] using region1_log hν1 hν4 hpprime.two_le hM hp4) hLpos
      have h2 : 0 ≤ Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 :=
        mul_nonneg hlogp (sq_nonneg _)
      calc Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * (ξ p) ^ (-(6 : ℤ))
          ≤ Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2
              * (8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ))) := mul_le_mul_of_nonneg_left h1 h2
        _ = 8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
              * (Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2) := by ring
    calc (∑ p ∈ Ps.filter (fun p => 4 * ν * p ^ 2 ≤ M),
        Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * (ξ p) ^ (-(6 : ℤ)))
        ≤ ∑ p ∈ Ps.filter (fun p => 4 * ν * p ^ 2 ≤ M),
            8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
              * (Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2) := Finset.sum_le_sum hpt
      _ = 8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
            * ∑ p ∈ Ps.filter (fun p => 4 * ν * p ^ 2 ≤ M),
                (Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ 8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (Cm ^ 2 * C1 + 1)
            * (1 + Real.log (ν : ℝ)) := by
          have hsub : (∑ p ∈ Ps.filter (fun p => 4 * ν * p ^ 2 ≤ M),
              Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2) ≤ Cm ^ 2 * C1 + Real.log (ν : ℝ) := by
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_)
              hsumg
            intro p hp _
            rw [hPs, Finset.mem_filter] at hp
            exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hp.1).1))
              (sq_nonneg _)
          have hL6 : 0 ≤ (Real.log (M : ℝ)) ^ (-(6 : ℤ)) := le_of_lt (zpow_pos hLpos _)
          have hB : (0 : ℝ) ≤ Cm ^ 2 * C1 := mul_nonneg (sq_nonneg _) hC1pos.le
          have hstep : Cm ^ 2 * C1 + Real.log (ν : ℝ)
              ≤ (Cm ^ 2 * C1 + 1) * (1 + Real.log (ν : ℝ)) := by
            nlinarith [hB, hlogν0]
          calc 8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
                * (∑ p ∈ Ps.filter (fun p => 4 * ν * p ^ 2 ≤ M),
                    (Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2))
              ≤ 8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (Cm ^ 2 * C1 + Real.log (ν : ℝ)) :=
                mul_le_mul_of_nonneg_left hsub (mul_nonneg (by norm_num) hL6)
            _ ≤ 8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * ((Cm ^ 2 * C1 + 1) * (1 + Real.log (ν : ℝ))) :=
                mul_le_mul_of_nonneg_left hstep (mul_nonneg (by norm_num) hL6)
            _ = 8 ^ 6 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (Cm ^ 2 * C1 + 1)
                  * (1 + Real.log (ν : ℝ)) := by ring
  -- region 2
  have hreg2 : (∑ p ∈ Ps.filter (fun p => ¬ (4 * ν * p ^ 2 ≤ M)),
      Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * (ξ p) ^ (-(6 : ℤ)))
      ≤ 20 * Cm ^ 2 * C2 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (1 + Real.log (ν : ℝ)) := by
    have hz1 : (1 : ℝ) ≤ (Real.log (M : ℝ)) ^ 12 / 4 := by
      have h1 : 8 * Real.log 2 ≤ Real.log (M : ℝ) := eight_log_two_le' hM
      have h2 : (2 : ℝ) ≤ 8 * Real.log 2 := by nlinarith [Real.log_two_gt_d9]
      have h3 : (2 : ℝ) ≤ Real.log (M : ℝ) := by linarith
      have h4 : (4 : ℝ) ≤ (Real.log (M : ℝ)) ^ 12 := by
        have h5 : (2 : ℝ) ^ 12 ≤ (Real.log (M : ℝ)) ^ 12 :=
          pow_le_pow_left₀ (by norm_num) h3 12
        norm_num at h5
        linarith [h5]
      linarith
    have hpt : ∀ p ∈ Ps.filter (fun p => ¬ (4 * ν * p ^ 2 ≤ M)),
        Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * (ξ p) ^ (-(6 : ℤ))
        ≤ 10 * Cm ^ 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpPs, hpM⟩ := hp
      push_neg at hpM
      rw [hPs, Finset.mem_filter] at hpPs
      obtain ⟨hpIcc, hpprime⟩ := hpPs
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hpIcc).1
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
      have hnd : ¬ p ∣ ν := not_dvd_of_four_mul_sq_gt hν1 hν4 hM hpM
      have hg2 : (g (p / Nat.gcd ν p)) ^ 2 ≤ (Cm / (p : ℝ)) ^ 2 := by
        rw [gcd_eq_one_of_not_dvd hpprime hnd, Nat.div_one]
        exact pow_le_pow_left₀ (hg0 p hpprime) (hg_le p hpprime) 2
      have h1 : Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2
          ≤ Real.log (p : ℝ) * (Cm / (p : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left hg2 hlogp
      have h2 : 0 ≤ Real.log (p : ℝ) * (Cm / (p : ℝ)) ^ 2 := mul_nonneg hlogp (sq_nonneg _)
      calc Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * (ξ p) ^ (-(6 : ℤ))
          ≤ (Real.log (p : ℝ) * (Cm / (p : ℝ)) ^ 2) * 10 :=
            mul_le_mul h1 (hξ10 p) (hξ0 p) h2
        _ = 10 * Cm ^ 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := by
            field_simp
    have hsum2 : (∑ p ∈ Ps.filter (fun p => ¬ (4 * ν * p ^ 2 ≤ M)),
        Real.log (p : ℝ) / (p : ℝ) ^ 2)
        ≤ C2 / Real.sqrt ((Real.log (M : ℝ)) ^ 12 / 4) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hC2 _ hz1 P)
      · intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpPs, hpM⟩ := hp
        push_neg at hpM
        rw [hPs, Finset.mem_filter] at hpPs
        rw [Finset.mem_filter]
        exact ⟨hpPs.1, hpPs.2, region2_log_lt hν1 hν4 hM hlog hpM⟩
      · intro p hp _
        rw [Finset.mem_filter] at hp
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hp.1).1))
          (by positivity)
    have hsq : Real.sqrt ((Real.log (M : ℝ)) ^ 12 / 4) = (Real.log (M : ℝ)) ^ 6 / 2 := by
      have h1 : Real.sqrt ((Real.log (M : ℝ)) ^ 12) = (Real.log (M : ℝ)) ^ 6 := by
        rw [show (Real.log (M : ℝ)) ^ 12 = ((Real.log (M : ℝ)) ^ 6) ^ 2 from by ring]
        exact Real.sqrt_sq (by positivity)
      have h2 : Real.sqrt (4 : ℝ) = 2 := by norm_num
      rw [Real.sqrt_div (by positivity), h1, h2]
    calc (∑ p ∈ Ps.filter (fun p => ¬ (4 * ν * p ^ 2 ≤ M)),
        Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * (ξ p) ^ (-(6 : ℤ)))
        ≤ ∑ p ∈ Ps.filter (fun p => ¬ (4 * ν * p ^ 2 ≤ M)),
            10 * Cm ^ 2 * (Real.log (p : ℝ) / (p : ℝ) ^ 2) := Finset.sum_le_sum hpt
      _ = 10 * Cm ^ 2 * (∑ p ∈ Ps.filter (fun p => ¬ (4 * ν * p ^ 2 ≤ M)),
            Real.log (p : ℝ) / (p : ℝ) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ 10 * Cm ^ 2 * (C2 / Real.sqrt ((Real.log (M : ℝ)) ^ 12 / 4)) :=
          mul_le_mul_of_nonneg_left hsum2 (by positivity)
      _ = 10 * Cm ^ 2 * (C2 / ((Real.log (M : ℝ)) ^ 6 / 2)) := by rw [hsq]
      _ = 20 * Cm ^ 2 * C2 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) := by
          rw [show (Real.log (M : ℝ)) ^ (-(6 : ℤ)) = (((Real.log (M : ℝ)) ^ 6)⁻¹) by
            simp [zpow_neg]]
          field_simp
          ring
      _ ≤ 20 * Cm ^ 2 * C2 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (1 + Real.log (ν : ℝ)) := by
          have h2 : (0 : ℝ) ≤ 20 * Cm ^ 2 * C2 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) := by
            have := zpow_pos hLpos (-(6 : ℤ)); positivity
          have h1 : (1 : ℝ) ≤ 1 + Real.log (ν : ℝ) := by linarith
          calc 20 * Cm ^ 2 * C2 * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
              = 20 * Cm ^ 2 * C2 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * 1 := by ring
            _ ≤ 20 * Cm ^ 2 * C2 * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * (1 + Real.log (ν : ℝ)) :=
                mul_le_mul_of_nonneg_left h1 h2
  rw [← Finset.sum_filter_add_sum_filter_not Ps (fun p => 4 * ν * p ^ 2 ≤ M)
    (fun p => Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * (ξ p) ^ (-(6 : ℤ)))]
  nlinarith [hreg1, hreg2]

/-- **§5**: the bound for the `ν`-th inner sum `T_ν`. -/
lemma abs_Tnu_le {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν M P : ℕ, Squarefree ν → 1 ≤ ν → ν ^ 4 ≤ M → 256 ≤ M → 2 ≤ P →
      (Real.log (M : ℝ)) ^ 6 ≤ (M : ℝ) ^ ((3 : ℝ) / 16) →
      |Tnu g M P ν| ≤ C * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
        * (ν.divisors.card : ℝ) * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
        * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := hbound
  have hgp : ∀ p : ℕ, p.Prime → 0 ≤ g p := fun p hp' => (hp p hp').1
  obtain ⟨C24, hC24pos, h24⟩ :=
    Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_le hmul hg1 hp ⟨Cg, hCg⟩ h9
  obtain ⟨Cpr, hCprpos, hpr⟩ :=
    Commons.NumberTheory.Sieve.sum_primes_log_mul_g_div_gcd_le hgp ⟨Cg, hCgpos, hCg⟩
  obtain ⟨Csm, hCsmpos, hsm⟩ := abs_Smup_le hmul hg1 hp ⟨Cg, hCg⟩ h9
  obtain ⟨Cps, hCpspos, hps⟩ := psum_bound hmul hg1 hgp ⟨Cg, hCgpos, hCg⟩
  refine ⟨max Cpr 1 * C24 + Csm * Cps, by positivity, ?_⟩
  intro ν M P hνsq hν1 hν4 hM hP2 hlog
  have hM2 : 2 ≤ M := by omega
  have hν2M : ν ^ 2 ≤ M := by nlinarith [hν1, hν4]
  set σ : ℝ := ∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) with hσ
  set τ : ℝ := (ν.divisors.card : ℝ) with hτ
  set L : ℝ := Real.log (M : ℝ) with hL
  have hLpos : 0 < L := by
    rw [hL]; exact Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hσ0 : 0 ≤ σ := by
    rw [hσ]; exact Finset.prod_nonneg (fun p _ => by positivity)
  have hτ0 : 0 ≤ τ := by rw [hτ]; positivity
  have hL6 : 0 ≤ L ^ (-(6 : ℤ)) := le_of_lt (zpow_pos hLpos _)
  have hS0 : 0 ≤ σ * τ * L ^ (-(6 : ℤ)) := mul_nonneg (mul_nonneg hσ0 hτ0) hL6
  rw [Tnu_eq hmul]
  set A : ℝ := ∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
    Real.log (p : ℝ) * g (p / Nat.gcd ν p) with hA
  set B : ℝ := ∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
    Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * Smup g ν p (M / p) with hBdef
  have hΛnn : 0 ≤ Real.log ((ν : ℝ) * (P : ℝ) + 2) := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν1
    have h2 : (0 : ℝ) ≤ (P : ℝ) := by positivity
    nlinarith
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg (fun p hp' => by
      rw [Finset.mem_filter] at hp'
      have hgnn : 0 ≤ g (p / Nat.gcd ν p) := by
        by_cases hd : p ∣ ν
        · rw [gcd_eq_self_of_dvd hd, Nat.div_self hp'.2.pos, hg1]; norm_num
        · rw [gcd_eq_one_of_not_dvd hp'.2 hd, Nat.div_one]; exact hgp p hp'.2
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hp'.1).1)) hgnn)
  have hAle : A ≤ max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) := by
    rw [hA]
    have h3 : Cpr ≤ max Cpr 1 := le_max_left _ _
    calc (∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime, Real.log (p : ℝ) * g (p / Nat.gcd ν p))
        ≤ Cpr * Real.log ((ν : ℝ) * (P : ℝ) + 2) := hpr ν P hνsq hP2
      _ ≤ max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) := by
          nlinarith [h3, hCprpos, hΛnn]
  have hSmu : |Smu g ν M| ≤ C24 * σ * τ * L ^ (-(6 : ℤ)) := by
    have h1 := h24 ν hνsq M hM2 hν2M
    rwa [← hσ, ← hτ, ← hL] at h1
  have hBle : |B| ≤ Csm * σ * τ * (Cps * L ^ (-(6 : ℤ)) * (1 + Real.log (ν : ℝ))) := by
    rw [hBdef]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hpt : ∀ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
        |Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * Smup g ν p (M / p)|
        ≤ Csm * σ * τ * (Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2
            * (Real.log (max 2 (((M / p : ℕ) : ℝ) / (2 * (ν : ℝ))))) ^ (-(6 : ℤ))) := by
      intro p hp'
      rw [Finset.mem_filter] at hp'
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hp'.1).1
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
      rw [abs_mul, abs_mul, abs_of_nonneg hlogp, abs_of_nonneg (sq_nonneg _)]
      have h1 := hsm ν p (M / p) hp'.2 hνsq hν1
      rw [← hσ, ← hτ] at h1
      calc Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * |Smup g ν p (M / p)|
          ≤ Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2
              * (Csm * σ * τ
                * (Real.log (max 2 (((M / p : ℕ) : ℝ) / (2 * (ν : ℝ))))) ^ (-(6 : ℤ))) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hlogp (sq_nonneg _))
        _ = Csm * σ * τ * (Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2
              * (Real.log (max 2 (((M / p : ℕ) : ℝ) / (2 * (ν : ℝ))))) ^ (-(6 : ℤ))) := by ring
    calc (∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
          |Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2 * Smup g ν p (M / p)|)
        ≤ ∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
            Csm * σ * τ * (Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2
              * (Real.log (max 2 (((M / p : ℕ) : ℝ) / (2 * (ν : ℝ))))) ^ (-(6 : ℤ))) :=
          Finset.sum_le_sum hpt
      _ = Csm * σ * τ * (∑ p ∈ (Finset.Icc 1 P).filter Nat.Prime,
            Real.log (p : ℝ) * (g (p / Nat.gcd ν p)) ^ 2
              * (Real.log (max 2 (((M / p : ℕ) : ℝ) / (2 * (ν : ℝ))))) ^ (-(6 : ℤ))) := by
          rw [Finset.mul_sum]
      _ ≤ Csm * σ * τ * (Cps * L ^ (-(6 : ℤ)) * (1 + Real.log (ν : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h2 := hps ν M P hν1 hν4 hM hlog
          rwa [← hL] at h2
  have hlogν_le : Real.log (ν : ℝ) ≤ Real.log ((ν : ℝ) * (P : ℝ) + 2) := by
    apply Real.log_le_log (by positivity)
    have h1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast (by omega : 1 ≤ P)
    have h2 : (0 : ℝ) ≤ (ν : ℝ) := by positivity
    nlinarith
  have step1 : |A * Smu g ν M| + |B| ≤ σ * τ * L ^ (-(6 : ℤ))
      * (C24 * (max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)))
          + Csm * Cps * (1 + Real.log (ν : ℝ))) := by
    have h1 : |A * Smu g ν M| ≤ A * (C24 * σ * τ * L ^ (-(6 : ℤ))) := by
      rw [abs_mul, abs_of_nonneg hA0]
      exact mul_le_mul_of_nonneg_left hSmu hA0
    have h2 : A * (C24 * σ * τ * L ^ (-(6 : ℤ)))
        ≤ (max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) * (C24 * σ * τ * L ^ (-(6 : ℤ))) :=
      mul_le_mul_of_nonneg_right hAle (by positivity)
    have h3 : (max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) * (C24 * σ * τ * L ^ (-(6 : ℤ)))
        = σ * τ * L ^ (-(6 : ℤ)) * (C24 * (max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)))) := by
      ring
    have h4 : Csm * σ * τ * (Cps * L ^ (-(6 : ℤ)) * (1 + Real.log (ν : ℝ)))
        = σ * τ * L ^ (-(6 : ℤ)) * (Csm * Cps * (1 + Real.log (ν : ℝ))) := by ring
    linarith [h1, h2, hBle, h3.le, h3.ge, h4.le, h4.ge]
  have step2 : σ * τ * L ^ (-(6 : ℤ))
      * (C24 * (max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)))
          + Csm * Cps * (1 + Real.log (ν : ℝ)))
      ≤ (max Cpr 1 * C24 + Csm * Cps) * σ * τ * L ^ (-(6 : ℤ))
          * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) := by
    have h2 : C24 * (max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)))
          + Csm * Cps * (1 + Real.log (ν : ℝ))
        ≤ (max Cpr 1 * C24 + Csm * Cps) * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) := by
      have hCsmps : 0 ≤ Csm * Cps := mul_nonneg hCsmpos.le hCpspos.le
      have h1 : Csm * Cps * (1 + Real.log (ν : ℝ))
          ≤ Csm * Cps * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (by linarith [hlogν_le]) hCsmps
      have he : C24 * (max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)))
          = max Cpr 1 * C24 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) := by ring
      linarith [h1, he.le, he.ge]
    calc σ * τ * L ^ (-(6 : ℤ))
          * (C24 * (max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)))
              + Csm * Cps * (1 + Real.log (ν : ℝ)))
        = (σ * τ * L ^ (-(6 : ℤ)))
            * (C24 * (max Cpr 1 * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)))
              + Csm * Cps * (1 + Real.log (ν : ℝ))) := by ring
      _ ≤ (σ * τ * L ^ (-(6 : ℤ)))
            * ((max Cpr 1 * C24 + Csm * Cps)
              * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left h2 hS0
      _ = (max Cpr 1 * C24 + Csm * Cps) * σ * τ * L ^ (-(6 : ℤ))
            * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) := by ring
  exact le_trans (le_trans (abs_add_le _ _) step1) step2

/-! ### The remainder part of §5 -/

/-- The sieve-part remainder of `T(x;y,z)` in §5. -/
noncomputable def RemS (r : ℕ → ℕ → ℝ) (lam : ℕ → ℝ) (Δ M P N : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P,
    (ArithmeticFunction.moebius b : ℝ) * ArithmeticFunction.vonMangoldt c *
      (if Squarefree (b * c) then
        ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν (b * c)) N else 0)

/-- `Tsum2` at integer scales. -/
lemma Tsum2_nat_eq (a lam : ℕ → ℝ) {N M P : ℕ} (hMN : M ≤ N) (hPN : P ≤ N) :
    Tsum2 a lam (N : ℝ) (M : ℝ) (P : ℝ)
      = ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P,
          (ArithmeticFunction.moebius b : ℝ)
            * (ArithmeticFunction.vonMangoldt c * Vb a lam (b * c) (N : ℝ)) := by
  rw [Tsum2, Nat.floor_natCast,
    filter_Icc_eq_Icc_floor (show (0 : ℝ) ≤ (M : ℝ) by positivity) (by simpa using hMN),
    filter_Icc_eq_Icc_floor (show (0 : ℝ) ≤ (P : ℝ) by positivity) (by simpa using hPN)]
  simp only [Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]

/-- Pointwise form of `V_b` valid at every modulus (the `if` accounts for the fact that
`V_b` vanishes at non-squarefree moduli when `a` is supported on squarefree numbers). -/
lemma Vb_decomp {a g : ℕ → ℝ} {r : ℕ → ℕ → ℝ} {lam : ℕ → ℝ} {N Δ : ℕ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (ha_sq : ∀ n : ℕ, ¬ Squarefree n → a n = 0)
    (hAd : Approx a g r (N : ℝ)) (hΔ : ∀ ν : ℕ, Δ < ν → lam ν = 0)
    {d : ℕ} (hd0 : 0 < d) :
    Vb a lam d (N : ℝ)
      = if Squarefree d then lamCoeff g lam Δ d * Acount a (N : ℝ)
          + ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν d) N else 0 := by
  by_cases hd : Squarefree d
  · rw [if_pos hd]
    exact Vb_nat_eq_coeff hmul hAd hΔ hd0 hd
  · rw [if_neg hd]
    exact Vb_eq_zero_of_not_squarefree ha_sq hd _

/-- **§5, the decomposition `T = A(x)·(main terms) + (remainder)`.** -/
lemma Tsum2_decomp {a g : ℕ → ℝ} {r : ℕ → ℕ → ℝ} {lam : ℕ → ℝ} {N M P Δ : ℕ}
    (hMN : M ≤ N) (hPN : P ≤ N)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (ha_sq : ∀ n : ℕ, ¬ Squarefree n → a n = 0)
    (hAd : Approx a g r (N : ℝ)) (hΔsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0) :
    Tsum2 a lam (N : ℝ) (M : ℝ) (P : ℝ)
      = Acount a (N : ℝ) * MainS g lam Δ M P + RemS r lam Δ M P N := by
  rw [Tsum2_nat_eq a lam hMN hPN]
  have hpt : ∀ b ∈ Finset.Icc 1 M, ∀ c ∈ Finset.Icc 1 P,
      (ArithmeticFunction.moebius b : ℝ)
          * (ArithmeticFunction.vonMangoldt c * Vb a lam (b * c) (N : ℝ))
      = Acount a (N : ℝ) * ((ArithmeticFunction.moebius b : ℝ)
            * (ArithmeticFunction.vonMangoldt c
              * (if Squarefree (b * c) then lamCoeff g lam Δ (b * c) else 0)))
        + (ArithmeticFunction.moebius b : ℝ)
            * (ArithmeticFunction.vonMangoldt c
              * (if Squarefree (b * c)
                then ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν (b * c)) N else 0)) := by
    intro b hb c hc
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
    have hbc0 : 0 < b * c := by positivity
    rw [Vb_decomp hmul ha_sq hAd hΔsupp hbc0]
    by_cases h : Squarefree (b * c)
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring
  rw [Finset.sum_congr rfl (fun b hb => Finset.sum_congr rfl (fun c hc => hpt b hb c hc))]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · rw [MainS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  · rw [RemS]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring

/-! ### The remainder estimate -/

/-- `1 ≤ τ(e)` for `e ≥ 1`. -/
private lemma one_le_card_divisors {e : ℕ} (he : 1 ≤ e) : (1 : ℝ) ≤ (e.divisors.card : ℝ) := by
  have h : 0 < e.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd e, by omega⟩⟩
  exact_mod_cast h

/-- `|μ(b)| ≤ 1` in `ℝ`. -/
private lemma abs_moebius_cast_le_one (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := n)
  exact_mod_cast h

/-- `L · L^{-3} = L^{-2}`. -/
private lemma log_mul_zpow (L : ℝ) (hL : L ≠ 0) :
    L * L ^ (-(3 : ℤ)) = L ^ (-(2 : ℤ)) := by
  rw [show L ^ (-(3 : ℤ)) = ((L ^ 3)⁻¹) by simp [zpow_neg],
    show L ^ (-(2 : ℤ)) = ((L ^ 2)⁻¹) by simp [zpow_neg]]
  field_simp

/-- `τ(e)² ≤ τ(e)⁵` for `e ≥ 1`. -/
private lemma card_divisors_sq_le_pow_five {e : ℕ} (he : 1 ≤ e) :
    ((e.divisors.card : ℝ)) ^ 2 ≤ ((e.divisors.card : ℝ)) ^ 5 := by
  have h1 : (1 : ℝ) ≤ (e.divisors.card : ℝ) := one_le_card_divisors he
  exact pow_le_pow_right₀ h1 (by norm_num)

/-- **§5, remainder estimate**: `|(sieve remainder)| ≤ 2A(x)(log x)^{-2}`.  Since the `Λ`-sum
vanishes unless `b·c` is squarefree and `λ` is squarefree-supported, the moduli `[ν, bc]` that
occur are squarefree and the squarefree form of `(R′)` suffices. -/
lemma abs_RemS_le {r : ℕ → ℕ → ℝ} {lam : ℕ → ℝ} {N M P D Δ : ℕ} {A Rem : ℝ}
    (hN : 2 ≤ N) (hM1 : 1 ≤ M) (hP1 : 1 ≤ P) (hMN : M ≤ N) (hPN : P ≤ N)
    (hA0 : 0 ≤ A)
    (hRem : ∀ m : ℕ, m ≤ N → RemainderSum r D m ≤ Rem) (hRem0 : 0 ≤ Rem)
    (hRem3 : Rem ≤ A * (Real.log (N : ℝ)) ^ (-(3 : ℤ)))
    (hΔMP : Δ * M * P ≤ D)
    (hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1) (hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0) :
    |RemS r lam Δ M P N| ≤ 2 * A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  set X : ℕ → ℝ := fun d => ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, |r (Nat.lcm ν d) N| with hX
  have hX0 : ∀ d : ℕ, 0 ≤ X d := by
    intro d; rw [hX]
    exact Finset.sum_nonneg (fun ν _ => abs_nonneg _)
  -- (A) drop `μ`, `Λ`, keeping the squarefree condition on `b * c`
  have hA : |RemS r lam Δ M P N|
      ≤ ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P,
          ArithmeticFunction.vonMangoldt c *
            (if Squarefree (b * c) then X (b * c) else 0) := by
    rw [RemS]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun b _ => Finset.abs_sum_le_sum_abs _ _)) ?_
    refine Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun c hc => ?_))
    have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt c := ArithmeticFunction.vonMangoldt_nonneg
    have hS : |(if Squarefree (b * c)
        then ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν (b * c)) N else 0)|
        ≤ (if Squarefree (b * c) then X (b * c) else 0) := by
      by_cases h : Squarefree (b * c)
      · rw [if_pos h, if_pos h, hX]
        have hstep1 : |∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν (b * c)) N|
            ≤ ∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |r (Nat.lcm ν (b * c)) N| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          apply Finset.sum_le_sum
          intro ν _
          rw [abs_mul]
        have hstep2 : (∑ ν ∈ Finset.Icc 1 Δ, |lam ν| * |r (Nat.lcm ν (b * c)) N|)
            ≤ ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, |r (Nat.lcm ν (b * c)) N| := by
          rw [Finset.sum_filter]
          apply Finset.sum_le_sum
          intro ν _
          by_cases hν : Squarefree ν
          · rw [if_pos hν]
            exact mul_le_of_le_one_left (abs_nonneg _) (hlam_le ν)
          · rw [if_neg hν, hlam_sq ν hν]; simp
        exact le_trans hstep1 hstep2
      · rw [if_neg h, if_neg h, abs_zero]
    rw [abs_mul, abs_mul, abs_of_nonneg hΛ0, mul_assoc]
    calc |((ArithmeticFunction.moebius b : ℤ) : ℝ)|
          * (ArithmeticFunction.vonMangoldt c
              * |(if Squarefree (b * c)
                  then ∑ ν ∈ Finset.Icc 1 Δ, lam ν * r (Nat.lcm ν (b * c)) N else 0)|)
        ≤ 1 * (ArithmeticFunction.vonMangoldt c
              * (if Squarefree (b * c) then X (b * c) else 0)) :=
          mul_le_mul (abs_moebius_cast_le_one b)
            (mul_le_mul_of_nonneg_left hS hΛ0)
            (mul_nonneg hΛ0 (abs_nonneg _)) (by norm_num)
      _ = ArithmeticFunction.vonMangoldt c
            * (if Squarefree (b * c) then X (b * c) else 0) := one_mul _
  -- (B) the squarefree `Λ`-fibre exchange
  have hB : (∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P,
        ArithmeticFunction.vonMangoldt c * (if Squarefree (b * c) then X (b * c) else 0))
      ≤ ∑ d ∈ (Finset.Icc 1 (M * P)).filter Squarefree, Real.log (d : ℝ) * X d :=
    sum_vonMangoldt_mul_le_sqfree hX0
  -- (C) replace `log d` by `log (MP)`
  have hC : (∑ d ∈ (Finset.Icc 1 (M * P)).filter Squarefree, Real.log (d : ℝ) * X d)
      ≤ Real.log ((M * P : ℕ) : ℝ)
          * ∑ d ∈ (Finset.Icc 1 (M * P)).filter Squarefree, X d := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun d hd => ?_)
    have hdI : d ∈ Finset.Icc 1 (M * P) := (Finset.mem_filter.mp hd).1
    have h1 : (d : ℝ) ≤ ((M * P : ℕ) : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hdI).2
    have h2 : 0 < (d : ℝ) := by
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hdI).1
      linarith
    exact mul_le_mul_of_nonneg_right (Real.log_le_log h2 h1) (hX0 d)
  -- (D) unravel `X` and swap the sums
  have hD : (∑ d ∈ (Finset.Icc 1 (M * P)).filter Squarefree, X d)
      ≤ RemainderSum r D N := by
    have hswap : (∑ d ∈ (Finset.Icc 1 (M * P)).filter Squarefree, X d)
        = ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
            ∑ d ∈ (Finset.Icc 1 (M * P)).filter Squarefree, |r (Nat.lcm ν d) N| := by
      rw [hX]
      exact Finset.sum_comm
    have hDM' : Δ * (M * P) ≤ D := by
      calc Δ * (M * P) = Δ * M * P := by ring
        _ ≤ D := hΔMP
    exact le_trans (le_of_eq hswap)
      (sum_lcm_le_remainderSum (Δ := Δ) (M := M * P) (D := D) hDM' N)
  have hE : Real.log ((M * P : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have h1 : ((M * P : ℕ) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul hMN hPN
    have h2 : 0 < ((M * P : ℕ) : ℝ) := by
      have : 0 < M * P := by positivity
      exact_mod_cast this
    have h3 := Real.log_le_log h2 h1
    rw [show ((N * N : ℕ) : ℝ) = (N : ℝ) * (N : ℝ) by push_cast; ring,
      Real.log_mul (by positivity) (by positivity)] at h3
    linarith
  have hlogMP0 : 0 ≤ Real.log ((M * P : ℕ) : ℝ) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((M * P : ℕ) : ℝ) := by
      have h : 1 ≤ M * P := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast h
    linarith
  calc |RemS r lam Δ M P N|
      ≤ ∑ b ∈ Finset.Icc 1 M, ∑ c ∈ Finset.Icc 1 P,
          ArithmeticFunction.vonMangoldt c
            * (if Squarefree (b * c) then X (b * c) else 0) := hA
    _ ≤ ∑ d ∈ (Finset.Icc 1 (M * P)).filter Squarefree, Real.log (d : ℝ) * X d := hB
    _ ≤ Real.log ((M * P : ℕ) : ℝ)
          * ∑ d ∈ (Finset.Icc 1 (M * P)).filter Squarefree, X d := hC
    _ ≤ Real.log ((M * P : ℕ) : ℝ) * RemainderSum r D N :=
        mul_le_mul_of_nonneg_left hD hlogMP0
    _ ≤ Real.log ((M * P : ℕ) : ℝ) * Rem := mul_le_mul_of_nonneg_left (hRem N le_rfl) hlogMP0
    _ ≤ 2 * Real.log (N : ℝ) * (A * (Real.log (N : ℝ)) ^ (-(3 : ℤ))) :=
        mul_le_mul hE hRem3 hRem0 (by positivity)
    _ = 2 * A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := by
        rw [show (2 : ℝ) * Real.log (N : ℝ) * (A * (Real.log (N : ℝ)) ^ (-(3 : ℤ)))
            = 2 * A * (Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (-(3 : ℤ))) by ring,
          log_mul_zpow _ (ne_of_gt hlogN)]

/-- **§5, main-term estimate**: `|MainS| ≤ C·B·(log M)^{-6}`. -/
lemma abs_MainS_le {g : ℕ → ℝ} {lam : ℕ → ℝ} {M P Δ : ℕ} {B : ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ)))
    (hP2 : 2 ≤ P) (hM256 : 256 ≤ M)
    (hlogM : (Real.log (M : ℝ)) ^ 6 ≤ (M : ℝ) ^ ((3 : ℝ) / 16))
    (hΔ4 : Δ ^ 4 ≤ M)
    (hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0)
    (hB : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        |lam ν| * g ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      |MainS g lam Δ M P| ≤ C * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * B := by
  obtain ⟨CT, hCTpos, hT⟩ := abs_Tnu_le hmul hg1 hp hbound h9
  refine ⟨CT, hCTpos, ?_⟩
  have hM2 : 1 < M := by omega
  have hL6 : 0 ≤ (Real.log (M : ℝ)) ^ (-(6 : ℤ)) :=
    le_of_lt (zpow_pos (Real.log_pos (by exact_mod_cast hM2)) _)
  have hgpn : ∀ p : ℕ, p.Prime → 0 ≤ g p := fun p hp' => (hp p hp').1
  rw [mainS_eq hmul hlam_sq]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hpt : ∀ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
      |lam ν * g ν * Tnu g M P ν|
      ≤ CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
          * ((|lam ν| * g ν * (ν.divisors.card : ℝ)
              * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
            * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) := by
    intro ν hν
    rw [Finset.mem_filter] at hν
    obtain ⟨hνIcc, hνsq⟩ := hν
    have hν1 : 1 ≤ ν := (Finset.mem_Icc.mp hνIcc).1
    have hνΔ : ν ≤ Δ := (Finset.mem_Icc.mp hνIcc).2
    have hν4 : ν ^ 4 ≤ M := le_trans (Nat.pow_le_pow_left hνΔ 4) hΔ4
    have hgnn : 0 ≤ g ν := g_nonneg_of_squarefree hmul hg1 hgpn hνsq
    have hTb := hT ν M P hνsq hν1 hν4 hM256 hP2 hlogM
    have h1 : |lam ν| * g ν * |Tnu g M P ν|
        ≤ |lam ν| * g ν * (CT * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
            * (ν.divisors.card : ℝ) * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
            * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hTb (mul_nonneg (abs_nonneg _) hgnn)
    rw [abs_mul, abs_mul, abs_of_nonneg hgnn]
    refine le_trans h1 (le_of_eq ?_)
    ring
  calc ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, |lam ν * g ν * Tnu g M P ν|
      ≤ ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
            * ((|lam ν| * g ν * (ν.divisors.card : ℝ)
                * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
              * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) := Finset.sum_le_sum hpt
    _ = CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ))
          * (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
              (|lam ν| * g ν * (ν.divisors.card : ℝ)
                * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
              * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2))) := by
        rw [← Finset.mul_sum]
    _ ≤ CT * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * B :=
        mul_le_mul_of_nonneg_left hB (mul_nonneg hCTpos.le hL6)

/-- **§5**: `T(x;y,z) ≪ A(x)((log y)^{-6} B + (log x)^{-2})`. -/
theorem Tsum2_eval {a g : ℕ → ℝ} {r : ℕ → ℕ → ℝ} {lam : ℕ → ℝ}
    {N M P D Δ : ℕ} {A Rem B : ℝ}
    (hN : 2 ≤ N) (hM1 : 1 ≤ M) (hP1 : 1 ≤ P) (hP2 : 2 ≤ P)
    (hMN : M ≤ N) (hPN : P ≤ N) (hM256 : 256 ≤ M)
    (hlogM : (Real.log (M : ℝ)) ^ 6 ≤ (M : ℝ) ^ ((3 : ℝ) / 16))
    (ha : ∀ n : ℕ, 0 ≤ a n) (ha_sq : ∀ n : ℕ, ¬ Squarefree n → a n = 0)
    (hA : A = Acount a (N : ℝ))
    (hAd : Approx a g r (N : ℝ))
    (hRem : ∀ m : ℕ, m ≤ N → RemainderSum r D m ≤ Rem) (hRem0 : 0 ≤ Rem)
    (hRem3 : Rem ≤ A * (Real.log (N : ℝ)) ^ (-(3 : ℤ)))
    (hΔMP : Δ * M * P ≤ D) (hΔ4 : Δ ^ 4 ≤ M)
    (hΔsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0)
    (hlam_sq : ∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0)
    (hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1)
    (hB : ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        |lam ν| * g ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (P : ℝ) + 2)) ≤ B)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p ∧ g p < 1)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (h9 : ∃ c C : ℝ, ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ C * (Real.log y) ^ (-(10 : ℤ))) :
    ∃ K : ℝ, 0 < K ∧
      |Tsum2 a lam (N : ℝ) (M : ℝ) (P : ℝ)|
        ≤ K * A * (B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) + (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
  obtain ⟨CM, hCMpos, hMain⟩ :=
    abs_MainS_le hgmul hg1 hp hbound h9 hP2 hM256 hlogM hΔ4 hlam_sq hB
  have hKpos : 0 < max CM 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _)
  refine ⟨max CM 2, hKpos, ?_⟩
  have hA0 : 0 ≤ A := by
    rw [hA, Acount, Nat.floor_natCast]
    exact Finset.sum_nonneg (fun n _ => ha n)
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogMpos : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hL6 : 0 ≤ (Real.log (M : ℝ)) ^ (-(6 : ℤ)) := le_of_lt (zpow_pos hlogMpos _)
  have hL2 : 0 ≤ (Real.log (N : ℝ)) ^ (-(2 : ℤ)) := le_of_lt (zpow_pos hlogNpos _)
  have hB0 : 0 ≤ B := by
    refine le_trans (Finset.sum_nonneg ?_) hB
    intro ν hν
    rw [Finset.mem_filter] at hν
    have hgnn : 0 ≤ g ν := g_nonneg_of_squarefree hgmul hg1 (fun p hp' => (hp p hp').1) hν.2
    have hprod : 0 ≤ ∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) :=
      Finset.prod_nonneg (fun p _ => by positivity)
    have hlog : 0 ≤ 1 + Real.log ((ν : ℝ) * (P : ℝ) + 2) := by
      have h1 : (1 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hν.1).1
      have h2 : (0 : ℝ) ≤ (P : ℝ) := by positivity
      have h3 : (1 : ℝ) ≤ (ν : ℝ) * (P : ℝ) + 2 := by nlinarith
      have h4 : 0 ≤ Real.log ((ν : ℝ) * (P : ℝ) + 2) := Real.log_nonneg h3
      linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hgnn) (by positivity))
      hprod) hlog
  have hRemB := abs_RemS_le hN hM1 hP1 hMN hPN hA0 hRem hRem0 hRem3 hΔMP hlam_le hlam_sq
  have hAabs : |Acount a (N : ℝ)| = A := by rw [← hA]; exact abs_of_nonneg hA0
  rw [Tsum2_decomp hMN hPN hgmul ha_sq hAd hΔsupp]
  calc |Acount a (N : ℝ) * MainS g lam Δ M P + RemS r lam Δ M P N|
      ≤ |Acount a (N : ℝ) * MainS g lam Δ M P| + |RemS r lam Δ M P N| := abs_add_le _ _
    _ = A * |MainS g lam Δ M P| + |RemS r lam Δ M P N| := by rw [abs_mul, hAabs]
    _ ≤ A * (CM * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * B)
          + 2 * A * (Real.log (N : ℝ)) ^ (-(2 : ℤ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hMain hA0) hRemB
    _ ≤ max CM 2 * A
          * (B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) + (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
        have h3 : CM ≤ max CM 2 := le_max_left _ _
        have h4 : (2 : ℝ) ≤ max CM 2 := le_max_right _ _
        have h5 : 0 ≤ max CM 2 := le_trans hCMpos.le h3
        calc A * (CM * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) * B)
              + 2 * A * (Real.log (N : ℝ)) ^ (-(2 : ℤ))
            = CM * (A * (B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)))) + 2 * (A * (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
              ring
          _ ≤ max CM 2 * (A * (B * (Real.log (M : ℝ)) ^ (-(6 : ℤ))))
                + max CM 2 * (A * (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right h3 (mul_nonneg hA0 (mul_nonneg hB0 hL6))
              · exact mul_le_mul_of_nonneg_right h4 (mul_nonneg hA0 hL2)
          _ = max CM 2 * A
                * (B * (Real.log (M : ℝ)) ^ (-(6 : ℤ)) + (Real.log (N : ℝ)) ^ (-(2 : ℤ))) := by
              ring

end

end Submission.ASP
