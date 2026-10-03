/-
# The `τ²`-weighted cubefree remainder sum for the Friedlander–Iwaniec sequence

The companion paper ("Asymptotic sieve for primes", §9) needs the `τ²`-weighted cubefree sum
`∑♭_{k ≤ D} τ(k)² |r_k(t)|` of the remainder of `X² + Y⁴` at a *crude* modulus cutoff
`D ≤ x^{141/200}` (the cutoff of the endgame, well inside the range where only the elementary
piece of `(R′₃)` is used).

This file records the bound that the endgame consumes:

    `∑♭_{k ≤ N} τ(k)² |r_k(t)|  ≤  C · A(x) · (log x)^B`   for `N ≤ x^{141/200}`, `t ≤ x`,

proved *without* any `(R₃)` input, by the pointwise split
`τ(d)²|r_d(t)| ≤ τ(d)²A_d(t) + A(t)·τ(d)²g(d)` (`FIr_abs_le_Ad`), the exchange of the `d`- and
`n`-sums `∑_{d ≤ D} τ(d)²A_d(t) ≤ ∑_{n ≤ t} a_n τ(n)³` (`sum_tau_sq_Ad_le`), the polylogarithmic
bound `∑_{n ≤ t} a_n τ(n)³ ≪ A(x)(log x)^B` (`sum_FIa_tau_cube_le`) and the elementary density
bound `∑♭_{k ≤ D} τ(k)²g(k) ≪ (log D)^{32}` (`sum_cubefree_tau_sq_FIg_le`).
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S40
import Submission.ASP.S31
import Submission.ASP.S22
import Submission.ASP.S21
import Submission.ASP.S35
import Submission.ASP.S36
import Submission.ASP.S34
import Submission.ASP.S33
import Submission.ASP.S32
import Submission.ASP.S9b
import Submission.ASP.S9d
import Submission.ASP.S37
import Submission.ASP_R3

set_option maxHeartbeats 4000000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem cubefree_tau_sq_FIr_le : ∃ X₀ : ℕ, ∃ C B : ℝ, 0 < C ∧
    ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x → ∀ N : ℕ, 3 ≤ N → (N : ℝ) ≤ (x : ℝ) ^ ((141 : ℝ) / 200) →
    (∑ k ∈ (Finset.Icc 1 N).filter (fun d => ∀ p ∈ d.primeFactors, d.factorization p ≤ 2),
        ((k.divisors.card : ℝ)) ^ 2 * |Submission.ASP.FIr k t|)
      ≤ C * (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ B := by
  obtain ⟨C2, B2, X2, hC2, hcube⟩ := Submission.ASP.sum_FIa_tau_cube_le
  obtain ⟨Cg, hCg, hg⟩ := Submission.ASP.sum_cubefree_tau_sq_FIg_le
  refine ⟨max ⌈X2⌉₊ 64, C2 + Cg * (2 : ℝ) ^ (32 : ℕ) + 1, max B2 32 + 1, by positivity, ?_⟩
  intro x hx t ht2 htx N hN3 hNx
  have hxX2 : X2 ≤ (x : ℝ) :=
    le_trans (Nat.le_ceil X2) (by exact_mod_cast (le_trans (le_max_left _ _) hx))
  have hx64 : 64 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_three, hx3]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) ≤ Real.log x := le_trans zero_le_one hL1
  -- rewrite the cubefree filter as the chapter's `CubefreeN`
  set F : Finset ℕ :=
    (Finset.Icc 1 N).filter (fun d => ∀ p ∈ d.primeFactors, d.factorization p ≤ 2) with hFdef
  have hFcf : F = (Finset.Icc 1 N).filter Submission.ASP.CubefreeN := rfl
  have hsub : F ⊆ Finset.Icc 1 N := by rw [hFdef]; exact Finset.filter_subset _ _
  have hA0 : (0 : ℝ) ≤ (Submission.Aseq x : ℝ) := Nat.cast_nonneg _
  have hAc_le : Submission.ASP.Acount Submission.ASP.FIa (t : ℝ) ≤ (Submission.Aseq x : ℝ) := by
    rw [Submission.ASP.FI_Acount_eq]
    have h3 : (Submission.Aseq t : ℝ) ≤ (Submission.Aseq x : ℝ) := by
      exact_mod_cast (Submission.ASP.Aseq_mono htx)
    have h2 : (0 : ℝ) ≤ (Submission.Aseq t : ℝ) := Nat.cast_nonneg _
    linarith
  -- ### Step 1: the pointwise split
  have hpt : ∀ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * |Submission.ASP.FIr k t|
      ≤ ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.Ad Submission.ASP.FIa k t
        + Submission.ASP.Acount Submission.ASP.FIa (t : ℝ)
            * (((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.FIg k) := by
    intro k _
    have h1 := Submission.ASP.FIr_abs_le_Ad k t
    have hτ : (0 : ℝ) ≤ ((k.divisors.card : ℝ)) ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hτ
    have h3 : ((k.divisors.card : ℝ)) ^ 2
          * (Submission.ASP.Ad Submission.ASP.FIa k t
              + Submission.ASP.FIg k * Submission.ASP.Acount Submission.ASP.FIa (t : ℝ))
        = ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.Ad Submission.ASP.FIa k t
          + Submission.ASP.Acount Submission.ASP.FIa (t : ℝ)
              * (((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.FIg k) := by ring
    linarith [h2, h3]
  have hsplit : (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * |Submission.ASP.FIr k t|)
      ≤ (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.Ad Submission.ASP.FIa k t)
        + Submission.ASP.Acount Submission.ASP.FIa (t : ℝ)
            * (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.FIg k) := by
    calc (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * |Submission.ASP.FIr k t|)
        ≤ ∑ k ∈ F, (((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.Ad Submission.ASP.FIa k t
            + Submission.ASP.Acount Submission.ASP.FIa (t : ℝ)
                * (((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.FIg k)) :=
          Finset.sum_le_sum hpt
      _ = (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.Ad Submission.ASP.FIa k t)
            + Submission.ASP.Acount Submission.ASP.FIa (t : ℝ)
                * (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.FIg k) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  -- ### Step 2: the congruence-sum piece, `∑ τ² A_k(t) ≤ ∑_{n ≤ t} a_n τ(n)³`
  have hS1 : (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.Ad Submission.ASP.FIa k t)
      ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2 := by
    refine le_trans ?_ (le_trans (Submission.ASP.sum_tau_sq_Ad_le t N) (hcube x hxX2 t ht2 htx))
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun n _ => Submission.ASP.FIa_nonneg n)))
  -- ### Step 3: the density piece, `∑♭ τ² g(k) ≪ (log x)^32`
  have hS3 : (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.FIg k)
      ≤ Cg * (2 : ℝ) ^ (32 : ℕ) * (Real.log x) ^ (32 : ℕ) := by
    have hNle : (N : ℝ) ≤ (x : ℝ) := by
      have h : (x : ℝ) ^ ((141 : ℝ) / 200) ≤ (x : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      rw [Real.rpow_one] at h
      linarith
    have hlogN : Real.log ((N : ℝ) + 2) ≤ 2 * Real.log x := by
      have h1 : (N : ℝ) + 2 ≤ 3 * (x : ℝ) := by linarith
      have h2 : Real.log ((N : ℝ) + 2) ≤ Real.log (3 * (x : ℝ)) :=
        Real.log_le_log (by linarith) h1
      rw [Real.log_mul (by norm_num) (by positivity)] at h2
      have h3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
      linarith
    have hnn : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hbase : (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.FIg k)
        ≤ Cg * (Real.log ((N : ℝ) + 2)) ^ (32 : ℕ) := by
      rw [hFcf]
      exact hg N (by omega)
    have hpow : (Real.log ((N : ℝ) + 2)) ^ (32 : ℕ)
        ≤ (2 * Real.log x) ^ (32 : ℕ) := pow_le_pow_left₀ hnn hlogN 32
    calc (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.FIg k)
        ≤ Cg * (Real.log ((N : ℝ) + 2)) ^ (32 : ℕ) := hbase
      _ ≤ Cg * (2 * Real.log x) ^ (32 : ℕ) := mul_le_mul_of_nonneg_left hpow hCg.le
      _ = Cg * (2 : ℝ) ^ (32 : ℕ) * (Real.log x) ^ (32 : ℕ) := by rw [mul_pow]; ring
  -- ### Step 4: monotonicity of the polylogarithmic factor
  have hB2le : B2 ≤ max B2 32 + 1 := by
    linarith [le_max_left B2 (32 : ℝ)]
  have h32le : (32 : ℝ) ≤ max B2 32 + 1 := by
    linarith [le_max_right B2 (32 : ℝ)]
  have hQ2 : (Real.log x) ^ B2 ≤ (Real.log x) ^ (max B2 32 + 1) :=
    Real.rpow_le_rpow_of_exponent_le hL1 hB2le
  have hQ32 : (Real.log x) ^ (32 : ℕ) ≤ (Real.log x) ^ (max B2 32 + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL1 h32le
  have hLp : (0 : ℝ) ≤ (Real.log x) ^ (max B2 32 + 1) := Real.rpow_nonneg hL0 _
  have hS30 : (0 : ℝ) ≤ ∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.FIg k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (by positivity) (Submission.ASP.FIg_nonneg k))
  have step1 : C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2
      ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (max B2 32 + 1) :=
    mul_le_mul_of_nonneg_left hQ2 (mul_nonneg hC2.le hA0)
  have step2 : (Submission.Aseq x : ℝ) * (Cg * (2 : ℝ) ^ (32 : ℕ) * (Real.log x) ^ (32 : ℕ))
      ≤ (Cg * (2 : ℝ) ^ (32 : ℕ)) * (Submission.Aseq x : ℝ)
          * (Real.log x) ^ (max B2 32 + 1) := by
    have he : (Submission.Aseq x : ℝ) * (Cg * (2 : ℝ) ^ (32 : ℕ) * (Real.log x) ^ (32 : ℕ))
        = (Cg * (2 : ℝ) ^ (32 : ℕ)) * (Submission.Aseq x : ℝ) * (Real.log x) ^ (32 : ℕ) := by
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hQ32
      (mul_nonneg (mul_nonneg hCg.le (by positivity)) hA0)
  have step3 : (C2 + Cg * (2 : ℝ) ^ (32 : ℕ)) * (Submission.Aseq x : ℝ)
        * (Real.log x) ^ (max B2 32 + 1)
      ≤ (C2 + Cg * (2 : ℝ) ^ (32 : ℕ) + 1) * (Submission.Aseq x : ℝ)
        * (Real.log x) ^ (max B2 32 + 1) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hA0) hLp
    linarith
  -- ### Step 5: assemble
  calc (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * |Submission.ASP.FIr k t|)
      ≤ (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.Ad Submission.ASP.FIa k t)
        + Submission.ASP.Acount Submission.ASP.FIa (t : ℝ)
            * (∑ k ∈ F, ((k.divisors.card : ℝ)) ^ 2 * Submission.ASP.FIg k) := hsplit
    _ ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ B2
        + (Submission.Aseq x : ℝ) * (Cg * (2 : ℝ) ^ (32 : ℕ) * (Real.log x) ^ (32 : ℕ)) := by
        refine add_le_add hS1 ?_
        exact mul_le_mul hAc_le hS3 hS30 hA0
    _ ≤ C2 * (Submission.Aseq x : ℝ) * (Real.log x) ^ (max B2 32 + 1)
        + (Cg * (2 : ℝ) ^ (32 : ℕ)) * (Submission.Aseq x : ℝ)
            * (Real.log x) ^ (max B2 32 + 1) := add_le_add step1 step2
    _ = (C2 + Cg * (2 : ℝ) ^ (32 : ℕ)) * (Submission.Aseq x : ℝ)
          * (Real.log x) ^ (max B2 32 + 1) := by ring
    _ ≤ (C2 + Cg * (2 : ℝ) ^ (32 : ℕ) + 1) * (Submission.Aseq x : ℝ)
          * (Real.log x) ^ (max B2 32 + 1) := step3

end

end Work.FIChain
