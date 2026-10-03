/-
# `Work.FIArea7.theorem2psi` — *FI* Theorem 2ψ, (26.2)

This file assembles *FI* §26: from Props. 23.1 and 23.2 it proves
`Work.FIArea7.Theorem2psi`, i.e. for all `N c d : ℕ`, `k : ℤ` and every bounded multiplicative
`4d`-periodic character `χ`,

  `‖∑_{n ≤ N} Λ(n)·λ(cn)‖ ≤ C·c·d·(|k|+1)·N^{76/77}`,

where `λ(n) = ∑^∧_{z z̄ = n} ψ(z)[z]` is the quadratic eigenvalue (23.1) with the Grössencharacter
`ψ = grossenChar χ k` (17.17).

The route is Vaughan's identity with the parameter `Y ≈ N^{3/19}`, split into the four terms
`S₀ + S₁ - S₂ + S₃` (`t2psi_vaughan_split`).  Using

* `S₀ = ∑_{n≤Y} Λ(n)λ(cn) ≪ c·Y` (trivially, via `‖λ(n)‖ ≤ 4 d(n)`);
* `S₁ = ∑_{a≤Y} μ(a)∑_{m≤N/a} log m λ(cam) ≪ c·d(|k|+1) N^{3/4} Y^{3/4}` (Prop. 23.2);
* `S₂ = ∑_{a,b≤Y} μ(a)Λ(b)∑_{m≤N/(ab)} λ(c(ab)m) ≪ c·d(|k|+1) N^{3/4} Y^{3/2}` (Prop. 23.2);
* `S₃ = ∑_{Y<a≤N/Y} μ(a)∑_{n≤N/a} w(n) λ(can) ≪ c·N·Y^{-1/12}` (Prop. 23.1 + Lemma 26.1),

one gets `N^{75/76}` at `Y = N^{3/19}`, strictly below the required `N^{76/77}`; all polylogarithmic
losses are absorbed into the constant.  For `c` large the trivial bound also suffices, which is how
the `log(cN)` factors of Props. 23.1/23.2 are eliminated.
-/
import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.t2psi_defs
import Submission.Work.FIArea7.t2psi_quadEigen_le
import Submission.Work.FIArea7.t2psi_vonMangoldt_tau_le
import Submission.Work.FIArea7.t2psi_low_weak
import Submission.Work.FIArea7.t2psi_S2_bound
import Submission.Work.FIArea7.t2psi_S3_bound3
import Submission.Work.FIArea7.t2psi_vaughan_split
import Submission.Work.FIArea7.t2psi_cmp_S0
import Submission.Work.FIArea7.t2psi_cmp_S1
import Submission.Work.FIArea7.t2psi_cmp_S2
import Submission.Work.FIArea7.t2psi_cmp_triv
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Elementary chain for four positive factors. -/
private lemma t2psi_mul4_le {a b c d a' b' c' d' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hd : d ≤ d') (ha0 : 0 < a) (hb0 : 0 < b) (hc0 : 0 < c) (hd0 : 0 < d) :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have ha' : 0 < a' := lt_of_lt_of_le ha0 ha
  have hb' : 0 < b' := lt_of_lt_of_le hb0 hb
  have hc' : 0 < c' := lt_of_lt_of_le hc0 hc
  have h1 : a * b ≤ a' * b' := mul_le_mul ha hb hb0.le ha'.le
  have h2 : a * b * c ≤ a' * b' * c' := mul_le_mul h1 hc hc0.le (mul_pos ha' hb').le
  exact mul_le_mul h2 hd hd0.le (mul_pos (mul_pos ha' hb') hc').le

/-- The trivial bound: `‖∑_{n ≤ N} Λ(n) λ(cn)‖ ≤ 16 C₈ c^{1/8} N (log(N+2))^3`, where `C₈` is a
constant with `d(n) ≤ C₈ n^{1/8}`. -/
private lemma t2psi_triv_bound (N c : ℕ) (k : ℤ) (chi : GaussianInt → ℂ) (C8 : ℝ)
    (hchi : ∀ z, ‖chi z‖ ≤ 1)
    (hC8 : ∀ n : ℕ, ((n.divisors.card : ℕ) : ℝ) ≤ C8 * (n : ℝ) ^ ((1:ℝ)/8)) :
    ‖∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)‖
      ≤ 16 * C8 * (c : ℝ) ^ ((1:ℝ)/8) * (N : ℝ) * (Real.log ((N : ℝ) + 2)) ^ (3:ℕ) := by
  have hC8ge1 : (1:ℝ) ≤ C8 := by
    have h := hC8 1
    simpa using h
  have hC8nn : (0:ℝ) ≤ C8 := le_trans (by norm_num) hC8ge1
  have hψ : ∀ z, ‖grossenChar chi k z‖ ≤ 1 := t2psi_norm_grossenChar chi hchi k
  have hpt : ∀ n ∈ Finset.Icc 1 N,
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)‖
        ≤ ArithmeticFunction.vonMangoldt n *
            (4 * C8 * (c : ℝ) ^ ((1:ℝ)/8) * ((n.divisors.card : ℕ) : ℝ)) := by
    intro n _
    have hcn : (((c * n).divisors.card : ℕ) : ℝ)
        ≤ ((c.divisors.card : ℕ) : ℝ) * ((n.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le c n
    have hcc : ((c.divisors.card : ℕ) : ℝ) ≤ C8 * (c : ℝ) ^ ((1:ℝ)/8) := hC8 c
    have hbc : ‖quadEigen (grossenChar chi k) (c * n)‖
        ≤ 4 * C8 * (c : ℝ) ^ ((1:ℝ)/8) * ((n.divisors.card : ℕ) : ℝ) := by
      refine le_trans (t2psi_quadEigen_le (grossenChar chi k) hψ (c * n)) ?_
      calc 4 * (((c * n).divisors.card : ℕ) : ℝ)
          ≤ 4 * (((c.divisors.card : ℕ) : ℝ) * ((n.divisors.card : ℕ) : ℝ)) := by linarith
        _ ≤ 4 * ((C8 * (c : ℝ) ^ ((1:ℝ)/8)) * ((n.divisors.card : ℕ) : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul_of_nonneg_right hcc (by positivity)
        _ = 4 * C8 * (c : ℝ) ^ ((1:ℝ)/8) * ((n.divisors.card : ℕ) : ℝ) := by ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_mul_of_nonneg_left hbc ArithmeticFunction.vonMangoldt_nonneg
  have hpos : (0:ℝ) ≤ 4 * C8 * (c : ℝ) ^ ((1:ℝ)/8) :=
    mul_nonneg (mul_nonneg (by norm_num) hC8nn) (Real.rpow_nonneg (Nat.cast_nonneg c) _)
  calc ‖∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)‖
      ≤ ∑ n ∈ Finset.Icc 1 N,
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n *
            (4 * C8 * (c : ℝ) ^ ((1:ℝ)/8) * ((n.divisors.card : ℕ) : ℝ)) :=
        Finset.sum_le_sum hpt
    _ = 4 * C8 * (c : ℝ) ^ ((1:ℝ)/8) *
          (∑ n ∈ Finset.Icc 1 N,
            ArithmeticFunction.vonMangoldt n * ((n.divisors.card : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ ≤ 4 * C8 * (c : ℝ) ^ ((1:ℝ)/8) *
          (4 * (N : ℝ) * (Real.log ((N : ℝ) + 2)) ^ (3:ℕ)) :=
        mul_le_mul_of_nonneg_left (t2psi_vonMangoldt_tau_le N) hpos
    _ = 16 * C8 * (c : ℝ) ^ ((1:ℝ)/8) * (N : ℝ) * (Real.log ((N : ℝ) + 2)) ^ (3:ℕ) := by ring

/-- Inserting the factor `d·(|k|+1) ≥ 1` and enlarging `K` to `CA + CB` — the final step of the
trivial case. -/
private lemma t2psi_final_ins {c d : ℕ} {k : ℤ} {K CA CB Yq : ℝ}
    (hc : (0:ℝ) ≤ (c:ℝ)) (hd1 : (1:ℝ) ≤ (d:ℝ)) (hk1 : (1:ℝ) ≤ |(k:ℝ)| + 1)
    (hK : (0:ℝ) ≤ K) (hKle : K ≤ CB) (hCA : (0:ℝ) ≤ CA) (hCB : (0:ℝ) < CB)
    (hY : (0:ℝ) ≤ Yq) :
    K * (c:ℝ) * Yq ≤ (CA + CB) * (c:ℝ) * (d:ℝ) * (|(k:ℝ)| + 1) * Yq := by
  have hdk : (1:ℝ) ≤ (d:ℝ) * (|(k:ℝ)| + 1) := by
    have h := mul_le_mul hd1 hk1 (by norm_num) (by positivity : (0:ℝ) ≤ (d:ℝ))
    simpa using h
  have h1 : K * (c:ℝ) ≤ K * (c:ℝ) * ((d:ℝ) * (|(k:ℝ)| + 1)) :=
    le_mul_of_one_le_right (mul_nonneg hK hc) hdk
  have h2 : K * (c:ℝ) * ((d:ℝ) * (|(k:ℝ)| + 1))
      ≤ (CA + CB) * (c:ℝ) * ((d:ℝ) * (|(k:ℝ)| + 1)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hc
    linarith
  calc K * (c:ℝ) * Yq = (K * (c:ℝ)) * Yq := by ring
    _ ≤ (K * (c:ℝ) * ((d:ℝ) * (|(k:ℝ)| + 1))) * Yq :=
        mul_le_mul_of_nonneg_right h1 hY
    _ ≤ ((CA + CB) * (c:ℝ) * ((d:ℝ) * (|(k:ℝ)| + 1))) * Yq :=
        mul_le_mul_of_nonneg_right h2 hY
    _ = (CA + CB) * (c:ℝ) * (d:ℝ) * (|(k:ℝ)| + 1) * Yq := by ring


/-- Enlarging `CA` to `CA + CB` in the final bound. -/
private lemma t2psi_ins_CA {c d : ℕ} {k : ℤ} {CA CB Yq : ℝ}
    (hc : (0:ℝ) ≤ (c:ℝ)) (hd1 : (1:ℝ) ≤ (d:ℝ)) (hk1 : (1:ℝ) ≤ |(k:ℝ)| + 1)
    (hCA : (0:ℝ) ≤ CA) (hCB : (0:ℝ) < CB) (hY : (0:ℝ) ≤ Yq) :
    CA * (c:ℝ) * (d:ℝ) * (|(k:ℝ)| + 1) * Yq
      ≤ (CA + CB) * (c:ℝ) * (d:ℝ) * (|(k:ℝ)| + 1) * Yq := by
  have h1 : CA ≤ CA + CB := by linarith
  have h2 : CA * (c:ℝ) ≤ (CA + CB) * (c:ℝ) :=
    mul_le_mul_of_nonneg_right h1 hc
  have h3 : CA * (c:ℝ) * (d:ℝ) ≤ (CA + CB) * (c:ℝ) * (d:ℝ) :=
    mul_le_mul_of_nonneg_right h2 (le_of_lt (lt_of_lt_of_le zero_lt_one hd1))
  have h4 : CA * (c:ℝ) * (d:ℝ) * (|(k:ℝ)| + 1)
      ≤ (CA + CB) * (c:ℝ) * (d:ℝ) * (|(k:ℝ)| + 1) :=
    mul_le_mul_of_nonneg_right h3 (le_of_lt (lt_of_lt_of_le zero_lt_one hk1))
  exact mul_le_mul_of_nonneg_right h4 hY


theorem theorem2psi (h31 : Work.FIArea7.Prop231) (h32 : Work.FIArea7.Prop232) :
    Work.FIArea7.Theorem2psi := by
  obtain ⟨Klow, Blow, hKlow0, hBlow0, hlow⟩ := t2psi_low_weak h32
  obtain ⟨KS2, BS2, hKS20, hBS20, hS2b⟩ := t2psi_S2_bound h32
  obtain ⟨KS3, BS3, hKS30, hBS30, hS3b⟩ := t2psi_S3_bound3 h31
  obtain ⟨C8, hC8pos, hC8⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1/8) (by norm_num)
  set Bf : ℝ := max 3 (max Blow (max BS2 BS3)) with hBfdef
  have h3Bf : (3:ℝ) ≤ Bf := le_max_left _ _
  have hBf0 : (0:ℝ) < Bf := lt_of_lt_of_le (by norm_num) h3Bf
  have hBlowBf : Blow ≤ Bf := le_trans (le_max_left _ _) (le_max_right _ _)
  have hBS2Bf : BS2 ≤ Bf :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hBS3Bf : BS3 ≤ Bf :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  set Kbig : ℝ := (Klow + KS2 + KS3 + 16 * C8 + 64) * (2:ℝ) ^ (Bf + 2) with hKbigdef
  have hKbigpos : (0:ℝ) < Kbig := by rw [hKbigdef]; positivity
  have hsum_nonneg : (0:ℝ) ≤ Klow + KS2 + KS3 + 16 * C8 + 64 := by positivity
  have h2nn : (0:ℝ) ≤ (2:ℝ) ^ (Bf + 2) := by positivity
  have h2one : (1:ℝ) ≤ (2:ℝ) ^ (Bf + 2) := Real.one_le_rpow (by norm_num) (by positivity)
  have h8big : (8:ℝ) ≤ (2:ℝ) ^ (Bf + 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by linarith : (3:ℝ) ≤ Bf + 2)
    have h2 : (2:ℝ) ^ (3:ℝ) = 8 := by norm_num
    rwa [h2] at h
  have hKlow_big : Klow * (2:ℝ) ^ ((3:ℝ)/4 + Blow) ≤ Kbig := by
    rw [hKbigdef]
    have h1 : Klow ≤ Klow + KS2 + KS3 + 16 * C8 + 64 := by linarith [hKS20, hKS30, hC8pos]
    have h2 : (2:ℝ) ^ ((3:ℝ)/4 + Blow) ≤ (2:ℝ) ^ (Bf + 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    exact mul_le_mul h1 h2 (by positivity) hsum_nonneg
  have hKS2_big : KS2 * (2:ℝ) ^ ((3:ℝ)/2 + BS2) ≤ Kbig := by
    rw [hKbigdef]
    have h1 : KS2 ≤ Klow + KS2 + KS3 + 16 * C8 + 64 := by linarith [hKlow0, hKS30, hC8pos]
    have h2 : (2:ℝ) ^ ((3:ℝ)/2 + BS2) ≤ (2:ℝ) ^ (Bf + 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    exact mul_le_mul h1 h2 (by positivity) hsum_nonneg
  have hKS3_le : KS3 ≤ Kbig := by
    rw [hKbigdef]
    have h1 : KS3 ≤ Klow + KS2 + KS3 + 16 * C8 + 64 := by linarith [hKlow0, hKS20, hC8pos]
    calc KS3 ≤ KS3 * (2:ℝ) ^ (Bf + 2) := le_mul_of_one_le_right hKS30.le h2one
      _ ≤ (Klow + KS2 + KS3 + 16 * C8 + 64) * (2:ℝ) ^ (Bf + 2) :=
          mul_le_mul_of_nonneg_right h1 h2nn
  have hC8_big : 128 * C8 + 64 ≤ Kbig := by
    rw [hKbigdef]
    have h1 : 16 * C8 + 64 ≤ Klow + KS2 + KS3 + 16 * C8 + 64 := by
      linarith [hKlow0, hKS20, hKS30]
    have h2 : (16 * C8 + 64) * (2:ℝ) ^ (Bf + 2)
        ≤ (Klow + KS2 + KS3 + 16 * C8 + 64) * (2:ℝ) ^ (Bf + 2) :=
      mul_le_mul_of_nonneg_right h1 h2nn
    have h3 : (16:ℝ) * C8 * (2:ℝ) ^ (Bf + 2) + 64 ≤ (16 * C8 + 64) * (2:ℝ) ^ (Bf + 2) := by
      nlinarith [h2one, hC8pos]
    calc 128 * C8 + 64 = 16 * C8 * 8 + 64 := by ring
      _ ≤ 16 * C8 * (2:ℝ) ^ (Bf + 2) + 64 := by
          have hpos : (0:ℝ) ≤ 16 * C8 := by positivity
          linarith [mul_le_mul_of_nonneg_left h8big hpos]
      _ ≤ (16 * C8 + 64) * (2:ℝ) ^ (Bf + 2) := h3
      _ ≤ (Klow + KS2 + KS3 + 16 * C8 + 64) * (2:ℝ) ^ (Bf + 2) := h2
  obtain ⟨CA, hCApos, hCA⟩ :=
    t2psi_absorb (4 * Kbig) Bf ((75:ℝ)/76 + 1/20000) (76/77) (by positivity) (le_of_lt hBf0) (by norm_num)
  obtain ⟨CB, hCBpos, hCB⟩ :=
    t2psi_absorb (16 * C8) 3 (1/77) (7/480) (by positivity) (by norm_num) (by norm_num)
  refine ⟨CA + CB, by positivity, ?_⟩
  intro N c d k chi hc hd hN hchi hmult hp1 hp2
  rcases Nat.lt_or_ge N 2 with hNlt | hNge
  · have hN1 : N = 1 := by omega
    have hzero : (∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          quadEigen (grossenChar chi k) (c * n)) = 0 := by
      rw [hN1, Finset.Icc_self, Finset.sum_singleton, ArithmeticFunction.vonMangoldt_apply_one]
      simp
    rw [hzero, norm_zero]
    have h1 : (0:ℝ) ≤ (CA + CB) := by linarith [hCApos, hCBpos]
    have h2 : (0:ℝ) ≤ (c:ℝ) := Nat.cast_nonneg c
    have h3 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have h4 : (0:ℝ) ≤ |(k:ℝ)| + 1 := by positivity
    have h5 : (0:ℝ) ≤ (N:ℝ) ^ (76/77 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) h5
  · have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNge
    have hNpos : (0:ℝ) < (N : ℝ) := by linarith
    have hNnn : (0:ℝ) ≤ (N:ℝ) := le_of_lt hNpos
    have hcpos : (0:ℝ) < (c : ℝ) := by exact_mod_cast hc
    have hcnn : (0:ℝ) ≤ (c:ℝ) := le_of_lt hcpos
    have hd1 : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hdnn : (0:ℝ) ≤ (d:ℝ) := le_of_lt (lt_of_lt_of_le zero_lt_one hd1)
    have hk1 : (1:ℝ) ≤ |(k : ℝ)| + 1 := by
      have := abs_nonneg (k:ℝ); linarith
    have hlogN2 : (0:ℝ) ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hbeta : (0:ℝ) ≤ (N:ℝ) ^ ((76:ℝ)/77) := Real.rpow_nonneg hNnn ((76:ℝ)/77)
    have hlog1 : (1:ℝ) ≤ Real.log ((N : ℝ) + 2) := by
      have h4 : (4:ℝ) ≤ (N : ℝ) + 2 := by linarith
      have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
        norm_num at h
        linarith
      have hlog4 : (1:ℝ) ≤ Real.log 4 := by
        rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
        push_cast
        linarith
      exact le_trans hlog4 (Real.log_le_log (by norm_num) h4)
    have hmain : (c : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/60) → ‖∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)‖ ≤ (CA + CB) * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((76:ℝ)/77) := by
      intro hcsmall
      set Y : ℕ := ⌊(N : ℝ) ^ ((3:ℝ)/19)⌋₊ + 1 with hYdef
      have hx0 : (0:ℝ) ≤ (N : ℝ) ^ ((3:ℝ)/19) := Real.rpow_nonneg hNnn _
      have hYgt : (N : ℝ) ^ ((3:ℝ)/19) < (Y : ℝ) := by
        have h := Nat.lt_floor_add_one ((N : ℝ) ^ ((3:ℝ)/19))
        rw [hYdef]
        push_cast
        linarith
      have hYle : (Y : ℝ) ≤ 2 * (N : ℝ) ^ ((3:ℝ)/19) := by
        have h1 := Nat.floor_le hx0
        have h2 : (1:ℝ) ≤ (N : ℝ) ^ ((3:ℝ)/19) :=
          Real.one_le_rpow (by linarith) (by norm_num)
        rw [hYdef]
        push_cast
        linarith
      have hY1 : 1 ≤ Y := by rw [hYdef]; omega
      have hYN : Y ≤ N := by
        have hN1 : (1:ℝ) < (N : ℝ) := by linarith
        have hxlt : (N : ℝ) ^ ((3:ℝ)/19) < (N : ℝ) := by
          calc (N : ℝ) ^ ((3:ℝ)/19) < (N : ℝ) ^ (1:ℝ) :=
                (Real.rpow_lt_rpow_left_iff hN1).mpr (by norm_num)
            _ = (N : ℝ) := Real.rpow_one _
        have hfl : ⌊(N : ℝ) ^ ((3:ℝ)/19)⌋₊ < N := (Nat.floor_lt hx0).mpr hxlt
        rw [hYdef]
        omega
      have hYleN : (Y:ℝ) ≤ (N:ℝ) := by exact_mod_cast hYN
      have hypos : (0:ℝ) ≤ Real.log ((Y : ℝ) + 2) := Real.log_nonneg (by linarith)
      have hlogY_le : Real.log ((Y : ℝ) + 2) ≤ Real.log ((N : ℝ) + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hlogcN : Real.log ((c : ℝ) * (N : ℝ) + 2) ≤ 2 * Real.log ((N : ℝ) + 2) := by
        have h5 : (c : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ (61/60 : ℝ) := by
          have h1 : (c : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/60) * (N : ℝ) :=
            mul_le_mul_of_nonneg_right hcsmall hNnn
          have h2 : (N : ℝ) ^ ((1:ℝ)/60) * (N : ℝ) = (N : ℝ) ^ ((1:ℝ)/60 + 1) := by
            calc (N : ℝ) ^ ((1:ℝ)/60) * (N : ℝ)
                = (N : ℝ) ^ ((1:ℝ)/60) * (N : ℝ) ^ (1:ℝ) := by rw [Real.rpow_one]
              _ = (N : ℝ) ^ ((1:ℝ)/60 + 1) := by rw [← Real.rpow_add hNpos]
          have h3 : (N : ℝ) ^ ((1:ℝ)/60 + 1) ≤ (N : ℝ) ^ (61/60 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          calc (c : ℝ) * (N : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/60) * (N : ℝ) := h1
            _ = (N : ℝ) ^ ((1:ℝ)/60 + 1) := h2
            _ ≤ (N : ℝ) ^ (61/60 : ℝ) := h3
        have h6 : (N : ℝ) ^ (61/60 : ℝ) + 2 ≤ ((N : ℝ) + 2) ^ (2:ℕ) := by
          have h4 : (N : ℝ) ^ (61/60 : ℝ) ≤ (N : ℝ) ^ (2:ℕ) := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          have h5' : (N : ℝ) ^ (2:ℕ) + 2 ≤ ((N : ℝ) + 2) ^ (2:ℕ) := by nlinarith [hN2]
          linarith
        calc Real.log ((c : ℝ) * (N : ℝ) + 2) ≤ Real.log (((N : ℝ) + 2) ^ (2:ℕ)) :=
              Real.log_le_log (by positivity) (by linarith)
          _ = 2 * Real.log ((N : ℝ) + 2) := by
              rw [Real.log_pow]; norm_num
      have hNexp : (N : ℝ) ^ ((75:ℝ)/76) ≤ (N : ℝ) ^ ((75:ℝ)/76 + 1/20000) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
      -- ## S₀
      have hS0 : ‖∑ n ∈ Finset.Icc 1 Y,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)‖
          ≤ Kbig * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76)
              * (Real.log ((N : ℝ) + 2)) ^ Bf := by
        refine le_trans (t2psi_triv_bound Y c k chi C8 hchi hC8) ?_
        refine le_trans (t2psi_cmp_S0 N c d k Y C8 Bf hNge hc hd hY1 hYle hYleN hC8pos h3Bf) ?_
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hC8_big
      -- ## S₁
      have hS1 : ‖∑ a ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius a : ℂ) *
            ∑ m ∈ Finset.Icc 1 (N / a),
              ((Real.log m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * (a * m))‖
          ≤ Kbig * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76)
              * (Real.log ((N : ℝ) + 2)) ^ Bf := by
        refine le_trans (hlow N c d k chi Y hN hc hd hY1 hchi hmult hp1 hp2) ?_
        refine le_trans (t2psi_cmp_S1 N c d k Y Klow Blow Bf hNge hc hd hY1 hYle hKlow0 (le_of_lt hBlow0)
          h3Bf hBlowBf hlogcN) ?_
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hKlow_big
      -- ## S₂
      have hS2 : ‖∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
            (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
              ∑ m ∈ Finset.Icc 1 (N / (a * b)),
                quadEigen (grossenChar chi k) (c * ((a * b) * m))‖
          ≤ Kbig * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76)
              * (Real.log ((N : ℝ) + 2)) ^ Bf := by
        refine le_trans (hS2b N c d Y k chi hN hc hd hY1 hchi hmult hp1 hp2) ?_
        refine le_trans (t2psi_cmp_S2 N c d k Y KS2 BS2 Bf hNge hc hd hY1 hYle hKS20 (le_of_lt hBS20)
          h3Bf hBS2Bf hlogcN) ?_
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hKS2_big
      have hS0beta : ‖∑ n ∈ Finset.Icc 1 Y,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)‖
          ≤ Kbig * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
              * (Real.log ((N : ℝ) + 2)) ^ Bf :=
        le_trans hS0 (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNexp (by positivity)) (by positivity))
      have hS1beta : ‖∑ a ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius a : ℂ) *
            ∑ m ∈ Finset.Icc 1 (N / a),
              ((Real.log m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * (a * m))‖
          ≤ Kbig * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
              * (Real.log ((N : ℝ) + 2)) ^ Bf :=
        le_trans hS1 (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNexp (by positivity)) (by positivity))
      have hS2beta : ‖∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
            (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
              ∑ m ∈ Finset.Icc 1 (N / (a * b)),
                quadEigen (grossenChar chi k) (c * ((a * b) * m))‖
          ≤ Kbig * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
              * (Real.log ((N : ℝ) + 2)) ^ Bf :=
        le_trans hS2 (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNexp (by positivity)) (by positivity))
      -- ## S₃
      have hS3 : ‖∑ a ∈ Finset.Icc (Y + 1) (N / Y), (ArithmeticFunction.moebius a : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / a),
              (∑ b ∈ n.divisors.filter (fun b => Y < b),
                  ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) *
                quadEigen (grossenChar chi k) (c * (a * n))‖
          ≤ Kbig * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
              * (Real.log ((N : ℝ) + 2)) ^ Bf := by
        have hcN : (c : ℝ) ≤ (N : ℝ) := by
          calc (c : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/60) := hcsmall
            _ ≤ (N : ℝ) ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            _ = (N : ℝ) := Real.rpow_one _
        refine le_trans (hS3b N c Y k chi hN hc hY1 hcN hYgt hchi hmult) ?_
        have hLog3 : (Real.log ((N : ℝ) + 2)) ^ BS3 ≤ (Real.log ((N : ℝ) + 2)) ^ Bf :=
          Real.rpow_le_rpow_of_exponent_le hlog1 hBS3Bf
        have hstep : KS3 * (c : ℝ) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
              * (Real.log ((N : ℝ) + 2)) ^ BS3
            ≤ Kbig * (c : ℝ) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
              * (Real.log ((N : ℝ) + 2)) ^ Bf :=
          t2psi_mul4_le hKS3_le le_rfl le_rfl hLog3 (by positivity) (by positivity)
            (by positivity) (by positivity)
        refine le_trans hstep ?_
        have hdk : (1:ℝ) ≤ (d : ℝ) * (|(k : ℝ)| + 1) := by
          have h := mul_le_mul hd1 hk1 (by norm_num) (by positivity : (0:ℝ) ≤ (d : ℝ))
          simpa using h
        have h1 : Kbig * (c : ℝ) ≤ Kbig * (c : ℝ) * ((d : ℝ) * (|(k : ℝ)| + 1)) :=
          le_mul_of_one_le_right (by positivity) hdk
        calc Kbig * (c : ℝ) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000) * (Real.log ((N : ℝ) + 2)) ^ Bf
            = (Kbig * (c : ℝ))
              * ((N : ℝ) ^ ((75:ℝ)/76 + 1/20000) * (Real.log ((N : ℝ) + 2)) ^ Bf) := by ring
          _ ≤ (Kbig * (c : ℝ) * ((d : ℝ) * (|(k : ℝ)| + 1)))
              * ((N : ℝ) ^ ((75:ℝ)/76 + 1/20000) * (Real.log ((N : ℝ) + 2)) ^ Bf) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = Kbig * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
              * (Real.log ((N : ℝ) + 2)) ^ Bf := by ring
      -- ## the Vaughan identity and the assembly
      have hva := t2psi_vaughan_split N Y c (grossenChar chi k) hY1 hYN
      have hT : ‖∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)‖
          ≤ 4 * Kbig * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
              * (Real.log ((N : ℝ) + 2)) ^ Bf := by
        rw [hva]
        have h2 := norm_add_le (∑ n ∈ Finset.Icc 1 Y, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)
            + ∑ a ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius a : ℂ) *
              ∑ m ∈ Finset.Icc 1 (N / a),
                ((Real.log m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * (a * m))
            - ∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
              (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
                ∑ m ∈ Finset.Icc 1 (N / (a * b)),
                  quadEigen (grossenChar chi k) (c * ((a * b) * m))) (∑ a ∈ Finset.Icc (Y + 1) (N / Y), (ArithmeticFunction.moebius a : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / a),
              (∑ b ∈ n.divisors.filter (fun b => Y < b),
                  ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) *
                quadEigen (grossenChar chi k) (c * (a * n)))
        have h3 := norm_sub_le (∑ n ∈ Finset.Icc 1 Y, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)
            + ∑ a ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius a : ℂ) *
              ∑ m ∈ Finset.Icc 1 (N / a),
                ((Real.log m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * (a * m))) (∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
              (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
                ∑ m ∈ Finset.Icc 1 (N / (a * b)),
                  quadEigen (grossenChar chi k) (c * ((a * b) * m)))
        have h4 := norm_add_le (∑ n ∈ Finset.Icc 1 Y, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)) (∑ a ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius a : ℂ) *
              ∑ m ∈ Finset.Icc 1 (N / a),
                ((Real.log m : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * (a * m)))
        linarith [h2, h3, h4, hS0beta, hS1beta, hS2beta, hS3]
      -- ## the final absorption
      have habs1 : 4 * Kbig * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000)
            * (Real.log ((N : ℝ) + 2)) ^ Bf
          = ((c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1))
            * (4 * Kbig * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000) * (Real.log ((N : ℝ) + 2)) ^ Bf) := by ring
      have habs2 : ((c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1))
            * (4 * Kbig * (N : ℝ) ^ ((75:ℝ)/76 + 1/20000) * (Real.log ((N : ℝ) + 2)) ^ Bf)
          ≤ ((c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)) * (CA * (N : ℝ) ^ ((76:ℝ)/77)) :=
          mul_le_mul_of_nonneg_left (hCA N hN) (by positivity)
      have habs3 : ((c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)) * (CA * (N : ℝ) ^ ((76:ℝ)/77))
          = CA * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((76:ℝ)/77) := by ring
      have habs4 : CA * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((76:ℝ)/77)
          ≤ (CA + CB) * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((76:ℝ)/77) :=
          t2psi_ins_CA hcnn hd1 hk1 (le_of_lt hCApos) hCBpos hbeta
      exact le_trans hT (le_trans habs1.le (le_trans habs2 (le_trans habs3.le habs4)))
    have htriv : (N : ℝ) ^ ((1:ℝ)/60) < (c : ℝ) → ‖∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen (grossenChar chi k) (c * n)‖ ≤ (CA + CB) * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (N : ℝ) ^ ((76:ℝ)/77) := by
      intro hcbig
      have htriv := t2psi_triv_bound N c k chi C8 hchi hC8
      have hcmp := t2psi_cmp_triv N c d k C8 CB hNge hc hd hC8pos hCBpos hcbig (hCB N hN)
      have hins := t2psi_final_ins hcnn hd1 hk1 (le_of_lt hCBpos) le_rfl (le_of_lt hCApos) hCBpos
        hbeta
      exact le_trans htriv (le_trans hcmp hins)
    by_cases hcsmall : (c : ℝ) ≤ (N : ℝ) ^ ((1:ℝ)/60)
    · exact hmain hcsmall
    · exact htriv (not_le.mp hcsmall)
end

end Work.FIArea7
