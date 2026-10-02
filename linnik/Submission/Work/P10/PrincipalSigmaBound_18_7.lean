/-
# `Work.P10.PrincipalSigmaBound_18_7`

The principal-character P3 bound of Heath-Brown Section 9 at the slope 18/7: for every M > 0 and
eps > 0 there is q0 such that for every modulus q >= q0, every test point s with
Re s = 1 + (18/7)/log q and |Im s| <= 4, and every lam1 in [0, M],

  Sigma(s, chi0) <= Re P3((18/7+lam1)/((s-1)log q)) + (18/7+lam1)*eps,

where Sigma = SigmaP3L is the HB smoothing functional (8.4) for the principal character mod q and
P3(X) = X + X^2 + (2/3)X^3 is the third polynomial of (4.12).

This is the 18/7-instance of the same computation as
Work.ZeroFreeTables.XY.PrincipalSigmaBoundD (the 17/5-instance).  The two generic ingredients
of that proof -- the pole-extraction reduction principalSigmaMasterD and the elementary
error-bracket bound errorBracket_le -- are stated for an arbitrary slope a and arbitrary
bound A >= a + lam1, so the whole argument transplants verbatim.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.XY.PrincipalSigmaBoundD

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option maxHeartbeats 2000000

namespace Work.P10

noncomputable section

theorem PrincipalSigmaBound_18_7 (M ε : ℝ) (hM : 0 < M) (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (lam₁ : ℝ) (s : ℂ),
      0 ≤ lam₁ → lam₁ ≤ M → s.re = 1 + (18/7) / Real.log q → |s.im| ≤ 4 →
      Work.ZeroFreeTables.SigmaP3L q (Real.log q) (1 : DirichletCharacter ℂ q) s (18/7) lam₁
        ≤ (Work.ZeroFreeTables.P3 ((((18/7 : ℝ) + lam₁) : ℂ)
              / ((s - 1) * ((Real.log q : ℝ) : ℂ)))).re + ((18/7 : ℝ) + lam₁) * ε := by
  obtain ⟨M₀, hM₀pos, hzB⟩ := Work.ZeroFreeTables.XY.PrincipalSigma.ZetaPoleBounded
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨C₃, hC₃pos, hC₃⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 3 (by norm_num)
  set C : ℝ := max C₁ (max C₂ C₃) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le hC₁pos (le_max_left _ _)
  have hC₁le : C₁ ≤ C := le_max_left _ _
  have hC₂le : C₂ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC₃le : C₃ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hA0 : (0 : ℝ) ≤ 18 / 7 + M := by linarith only [hM]
  obtain ⟨L₀, hL₀1, hL₀bd⟩ :=
    Work.ZeroFreeTables.Table4.principalArith M₀ C (18 / 7 + M) ε hM₀pos hCpos hA0 hε
  refine ⟨max 3 (⌈Real.exp (max L₀ 2)⌉₊ + 1), fun q hq hNe lam₁ s hlam0 hlamM hre him => ?_⟩
  have hq3 : 3 ≤ q := le_trans (le_max_left _ _) hq
  have hqexp : ⌈Real.exp (max L₀ 2)⌉₊ + 1 ≤ q := le_trans (le_max_right _ _) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hexp_le : Real.exp (max L₀ 2) ≤ (q : ℝ) := by
    have h2 : Real.exp (max L₀ 2) ≤ ((⌈Real.exp (max L₀ 2)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : (((⌈Real.exp (max L₀ 2)⌉₊ + 1 : ℕ)) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqexp
    push_cast at h3
    linarith only [h2, h3]
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hLge' : max L₀ 2 ≤ L := by
    rw [hLdef]
    have h := Real.log_le_log (Real.exp_pos (max L₀ 2)) hexp_le
    rwa [Real.log_exp] at h
  have hLge : L₀ ≤ L := le_trans (le_max_left _ _) hLge'
  have hL2 : (2 : ℝ) ≤ L := le_trans (le_max_right _ _) hLge'
  have hL1 : 1 ≤ L := le_trans hL₀1 hLge
  have hLpos : 0 < L := by linarith only [hL2]
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hsre1 : 1 < s.re := by
    rw [hre]
    have h : 0 < (18 : ℝ) / 7 / L := div_pos (by norm_num) hLpos
    linarith only [h]
  have hsre4 : s.re ≤ 4 := by
    rw [hre]
    have h : (18 : ℝ) / 7 / L ≤ 3 := by
      rw [div_le_iff₀ hLpos]
      linarith only [hL2]
    linarith only [h]
  have him5 : |s.im| ≤ 5 := by linarith only [him]
  obtain ⟨hz0, hz1, hz2⟩ := hzB s hsre1 hsre4 him5
  obtain ⟨hE0, hE1, hE2⟩ :=
    Work.ZeroFreeTables.XY.PrincipalSigma.EulerFactorBounds q (le_of_lt hsre1)
  have hd0 := Work.ZeroFreeTables.XY.PrincipalSigma.LogDerivPrincipalDecomp q 0 (by norm_num) hsre1
  have hd1 := Work.ZeroFreeTables.XY.PrincipalSigma.LogDerivPrincipalDecomp q 1 (by norm_num) hsre1
  have hd2 := Work.ZeroFreeTables.XY.PrincipalSigma.LogDerivPrincipalDecomp q 2 (by norm_num) hsre1
  have hd0' : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
      = logDeriv riemannZeta s
        + ∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1) := by
    simpa only [iteratedDeriv_zero] using hd0
  set S₁ : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) with hS₁def
  set S₂ : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) with hS₂def
  set S₃ : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) with hS₃def
  have hS₁bd : S₁ ≤ C * (Real.log L + 2) ^ 2 := by
    have h := hC₁ q hq3
    have h' : S₁ ≤ C₁ * (Real.log L) ^ 2 := by
      rw [hS₁def]
      simpa only [pow_one, ← hLdef] using h
    refine le_trans h' ?_
    have h1 : (Real.log L) ^ 2 ≤ (Real.log L + 2) ^ 2 :=
      pow_le_pow_left₀ hlogL0 (by linarith only []) 2
    have h2 : C₁ * (Real.log L) ^ 2 ≤ C₁ * (Real.log L + 2) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hC₁pos)
    have h3 : C₁ * (Real.log L + 2) ^ 2 ≤ C * (Real.log L + 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hC₁le (by positivity)
    linarith only [h2, h3]
  have hS₂bd : S₂ ≤ C * (Real.log L + 2) ^ 3 := by
    have h := hC₂ q hq3
    have h' : S₂ ≤ C₂ * (Real.log L) ^ 3 := by
      rw [hS₂def]
      simpa only [← hLdef] using h
    refine le_trans h' ?_
    have h1 : (Real.log L) ^ 3 ≤ (Real.log L + 2) ^ 3 :=
      pow_le_pow_left₀ hlogL0 (by linarith only []) 3
    have h2 : C₂ * (Real.log L) ^ 3 ≤ C₂ * (Real.log L + 2) ^ 3 :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hC₂pos)
    have h3 : C₂ * (Real.log L + 2) ^ 3 ≤ C * (Real.log L + 2) ^ 3 :=
      mul_le_mul_of_nonneg_right hC₂le (by positivity)
    linarith only [h2, h3]
  have hS₃bd : S₃ ≤ C * (Real.log L + 2) ^ 4 := by
    have h := hC₃ q hq3
    have h' : S₃ ≤ C₃ * (Real.log L) ^ 4 := by
      rw [hS₃def]
      simpa only [← hLdef] using h
    refine le_trans h' ?_
    have h1 : (Real.log L) ^ 4 ≤ (Real.log L + 2) ^ 4 :=
      pow_le_pow_left₀ hlogL0 (by linarith only []) 4
    have h2 : C₃ * (Real.log L) ^ 4 ≤ C₃ * (Real.log L + 2) ^ 4 :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hC₃pos)
    have h3 : C₃ * (Real.log L + 2) ^ 4 ≤ C * (Real.log L + 2) ^ 4 :=
      mul_le_mul_of_nonneg_right hC₃le (by positivity)
    linarith only [h2, h3]
  have hS₁0 : 0 ≤ S₁ := by
    rw [hS₁def]
    refine Finset.sum_nonneg fun p hp => div_nonneg ?_ (Nat.cast_nonneg p)
    exact Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)))
  have hS₂0 : 0 ≤ S₂ := by
    rw [hS₂def]
    exact Finset.sum_nonneg fun p hp => div_nonneg (by positivity) (Nat.cast_nonneg p)
  have hS₃0 : 0 ≤ S₃ := by
    rw [hS₃def]
    exact Finset.sum_nonneg fun p hp => div_nonneg (by positivity) (Nat.cast_nonneg p)
  have hF0 : ‖(∑ p ∈ q.primeFactors, (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ s - 1))‖ ≤ 2 * S₁ := by
    have hsum : (∑ p ∈ q.primeFactors, 2 * Real.log (p : ℝ) / (p : ℝ)) = 2 * S₁ := by
      rw [hS₁def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [← hsum]
    exact hE0
  have hF1 : ‖iteratedDeriv 1 (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖ ≤ 4 * S₂ := by
    have hsum : (∑ p ∈ q.primeFactors, 4 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) = 4 * S₂ := by
      rw [hS₂def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [← hsum]
    exact hE1
  have hF2 : ‖iteratedDeriv 2 (fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1)) s‖ ≤ 16 * S₃ := by
    have hsum : (∑ p ∈ q.primeFactors, 16 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) = 16 * S₃ := by
      rw [hS₃def, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [← hsum]
    exact hE2
  have hm := Work.ZeroFreeTables.XY.principalSigmaMasterD (q := q) (s := s) (a := 18 / 7)
    (lam₁ := lam₁) (L := L) (M := M₀) (S1 := S₁) (S2 := S₂) (S3 := S₃)
    (W := (Work.ZeroFreeTables.P3 ((((18/7 : ℝ) + lam₁) : ℂ)
            / ((s - 1) * ((L : ℝ) : ℂ)))).re)
    (by push_cast; ring)
    hLpos hsre1 (by norm_num) hlam0 hz0 hz1 hz2 hF0 hF1 hF2 hd0' hd1 hd2
  have hbr : ((18 : ℝ) / 7 + lam₁) / L * M₀ + (((18 : ℝ) / 7 + lam₁) / L) ^ 2 * M₀
      + (1 / 3) * (((18 : ℝ) / 7 + lam₁) / L) ^ 3 * M₀
      + ((18 : ℝ) / 7 + lam₁) / L * (2 * S₁)
      + (((18 : ℝ) / 7 + lam₁) / L) ^ 2 * (4 * S₂)
      + (1 / 3) * (((18 : ℝ) / 7 + lam₁) / L) ^ 3 * (16 * S₃) ≤ ((18 : ℝ) / 7 + lam₁) * ε :=
    Work.ZeroFreeTables.XY.errorBracket_le (M₀ := M₀) (C := C) (A := 18 / 7 + M) (ε := ε)
      (α := (18 : ℝ) / 7 + lam₁) (S₁ := S₁) (S₂ := S₂) (S₃ := S₃) hL1 (by linarith only [hlam0])
      (by linarith only [hlamM]) hA0 (le_of_lt hM₀pos) (le_of_lt hCpos) hS₁bd hS₂bd hS₃bd hS₁0 hS₂0 hS₃0
      (hL₀bd L hLge)
  have hfin : Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s (18 / 7) lam₁
      ≤ (Work.ZeroFreeTables.P3 ((((18/7 : ℝ) + lam₁) : ℂ)
            / ((s - 1) * ((L : ℝ) : ℂ)))).re + (18 / 7 + lam₁) * ε := by
    refine le_trans hm ?_
    linarith only [hbr]
  simpa only [hLdef] using hfin

end

end Work.P10
