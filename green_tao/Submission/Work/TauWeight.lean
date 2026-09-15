import Mathlib
import Submission.Commons.NumberTheory.Sieve.primeFactors_weight_moment
import Submission.Commons.Data.ZMod.sum_dist_to_zero

/-!
# The correlation weight `τ` for the Goldston–Yıldırım majorant (Green–Tao §9, `additive-weights`)

Green–Tao's weight in the correlation condition is essentially

  `τ(n) = A · ∏_{p | n} (1 + p^{-1/2})^{B}`  (`n ≥ 1`),   `τ(0) = (1 + log N)^{c}`.

This file proves the *moment bound* `𝔼 τ^q = O_{A,B,c,q}(1)` uniformly in `N`, which supplies the
`C m q` of `CorrCond`.  The key inputs are the arithmetic average
`Commons.NumberTheory.Sieve.primeFactors_weight_moment` and the reindexing
`Commons.Data.ZMod.sum_dist_to_zero`.
-/

namespace GYMaj

open Finset

/-- `log (1 + s) ≤ 2 * sqrt s + 2` for `s ≥ 0`. -/
lemma log_one_add_le_two_sqrt_add_two {s : ℝ} (hs : 0 ≤ s) :
    Real.log (1 + s) ≤ 2 * Real.sqrt s + 2 := by
  have h1 : 0 ≤ 1 + s := by linarith
  have h2 : Real.log (1 + s) ≤ (1 + s) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
    Real.log_le_rpow_div h1 (by norm_num)
  have h3 : (1 + s) ^ (1 / 2 : ℝ) = Real.sqrt (1 + s) := by
    rw [Real.sqrt_eq_rpow]
  rw [h3] at h2
  have h4 : Real.sqrt (1 + s) ≤ Real.sqrt s + 1 := by
    have h5 : (1 + s : ℝ) ≤ (Real.sqrt s + 1) ^ 2 := by
      have h6 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
      nlinarith [Real.sqrt_nonneg s]
    calc Real.sqrt (1 + s) ≤ Real.sqrt ((Real.sqrt s + 1) ^ 2) := Real.sqrt_le_sqrt h5
      _ = Real.sqrt s + 1 := Real.sqrt_sq (by positivity)
  linarith

/-- The weight `A · ∏_{p | d} (1 + p^{-1/2})^B` for `d ≥ 1`, and `(1 + log N)^c` for `d = 0`. -/
noncomputable def tauNat (A : ℝ) (B : ℕ) (c : ℕ) (N : ℕ) (d : ℕ) : ℝ :=
  if d = 0 then (1 + Real.log (N : ℝ)) ^ c
  else A * (∏ p ∈ d.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)))) ^ B

/-- `tauNat` is nonnegative for `A ≥ 0`. -/
lemma tauNat_nonneg {A : ℝ} (hA : 0 ≤ A) (B c N : ℕ) (d : ℕ) : 0 ≤ tauNat A B c N d := by
  unfold tauNat
  split_ifs with h
  · exact pow_nonneg (by positivity) _
  · apply mul_nonneg hA
    exact pow_nonneg (Finset.prod_nonneg (fun p hp => by
      have hp0 : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg p
      linarith [Real.rpow_nonneg hp0 (-(1/2:ℝ))])) _

/-- Main arithmetic estimate: `(1 + log p)^{c q} / p ≤ exp (c² q² + 2 c q)`. -/
lemma rpow_log_div_le_exp {p c q : ℕ} (hp : 1 ≤ p) :
    (1 + Real.log (p : ℝ)) ^ (c * q) / (p : ℝ)
      ≤ Real.exp ((c : ℝ) ^ 2 * (q : ℝ) ^ 2 + 2 * (c : ℝ) * (q : ℝ)) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  set s := Real.log (p : ℝ) with hs
  have hbase : (0 : ℝ) < 1 + s := by linarith
  have hpos : (0 : ℝ) < (1 + s) ^ (c * q) / (p : ℝ) := by positivity
  rw [← Real.exp_log hpos, Real.log_div (by positivity) (ne_of_gt hpR),
      Real.log_pow, ← hs]
  apply Real.exp_le_exp.mpr
  have hle := log_one_add_le_two_sqrt_add_two hlogp
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hlogp
  have hamgm : 2 * ((c : ℝ) * q) * Real.sqrt s ≤ s + ((c : ℝ) * q) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt s - (c : ℝ) * q)]
  have hmul := mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ (c : ℝ) * q)
  simp only [Nat.cast_mul] at hmul ⊢
  nlinarith [hamgm, hmul]

/-- **The moment bound of the correlation weight.**  For `A ≥ 0` the weight `tauNat A B c p`
has `q`-th moment bounded independently of the prime `p`. -/
theorem tauNat_moment_bound {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) {A : ℝ} (hA : 0 ≤ A)
    (B c q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (p : ℝ)⁻¹ * ∑ x : ZMod p, (tauNat A B c p (min x.val (p - x.val))) ^ q ≤ C := by
  obtain ⟨Cw, hCw0, hCw⟩ := Commons.NumberTheory.Sieve.primeFactors_weight_moment (B * q)
  refine ⟨Real.exp ((c : ℝ) ^ 2 * (q : ℝ) ^ 2 + 2 * (c : ℝ) * (q : ℝ)) + 2 * A ^ q * Cw,
    by positivity, ?_⟩
  classical
  set f : ℕ → ℝ := fun d => tauNat A B c p d with hf
  set S : ℝ := ∑ d ∈ Finset.Icc 1 (p / 2), f d ^ q with hS
  have hsum : ∑ x : ZMod p, (tauNat A B c p (min x.val (p - x.val))) ^ q
      = f 0 ^ q + 2 * S := by
    have h := Commons.Data.ZMod.sum_dist_to_zero p hp (fun d => f d ^ q)
    rw [hS]; simpa [hf] using h
  rw [hsum]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hf0 : f 0 = (1 + Real.log (p : ℝ)) ^ c := by simp [hf, tauNat]
  -- The half-range sum vs the arithmetic average estimate.
  have hIcc : (p : ℝ)⁻¹ * S ≤ A ^ q * Cw := by
    have hsub : Finset.Icc 1 (p / 2) ⊆ Finset.Icc 1 p := by
      intro d hd
      rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 (Nat.div_le_self p 2)⟩
    have hstep : S ≤ A ^ q * ∑ d ∈ Finset.Icc 1 p,
        (∏ p' ∈ d.primeFactors, (1 + (p' : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (B * q) := by
      rw [hS]
      have hmono : ∑ d ∈ Finset.Icc 1 (p / 2), f d ^ q
          ≤ ∑ d ∈ Finset.Icc 1 p, f d ^ q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun d _ _ => pow_nonneg (tauNat_nonneg hA B c p d) q)
      refine le_trans hmono (le_of_eq ?_)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd0 : d ≠ 0 := by omega
      have hfd : f d = A * (∏ p' ∈ d.primeFactors, (1 + (p' : ℝ) ^ (-(1 / 2 : ℝ)))) ^ B := by
        simp only [hf, tauNat, if_neg hd0]
      rw [hfd, mul_pow, ← pow_mul]
    have hbound := hCw p (by omega : 1 ≤ p)
    rw [inv_mul_le_iff₀ hpR] at hbound
    have hAq : (0 : ℝ) ≤ A ^ q := pow_nonneg hA q
    have := mul_le_mul_of_nonneg_left hbound hAq
    rw [inv_mul_le_iff₀ hpR]
    calc S ≤ A ^ q * ∑ d ∈ Finset.Icc 1 p,
            (∏ p' ∈ d.primeFactors, (1 + (p' : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (B * q) := hstep
      _ ≤ A ^ q * ((p : ℝ) * Cw) := this
      _ = (p : ℝ) * (A ^ q * Cw) := by ring
  -- split the sum
  have hsplit : (p : ℝ)⁻¹ * (f 0 ^ q + 2 * S)
      = f 0 ^ q / (p : ℝ) + 2 * ((p : ℝ)⁻¹ * S) := by
    field_simp
  rw [hsplit]
  have hzero : f 0 ^ q / (p : ℝ)
      ≤ Real.exp ((c : ℝ) ^ 2 * (q : ℝ) ^ 2 + 2 * (c : ℝ) * (q : ℝ)) := by
    rw [hf0, ← pow_mul]
    exact rpow_log_div_le_exp (p := p) (c := c) (q := q) (by omega : 1 ≤ p)
  have h2 : 2 * ((p : ℝ)⁻¹ * S) ≤ 2 * (A ^ q * Cw) :=
    mul_le_mul_of_nonneg_left hIcc (by norm_num)
  linarith [hzero, h2]

end GYMaj
