import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.log_mul_log_le_sqrt
import Submission.Work.BMF.dyadic_prime_card_le
import Submission.Work.BMF.norm_cpow_neg_I_mul
import Submission.Work.BMF.Ioc_filter_prime_subset_primesIn
import Submission.Work.BMF.primesIn_sdiff_card_le_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset Real Complex ArithmeticFunction

/-- The unimodular factor `n ↦ n^{-iu}`. -/
noncomputable def pwt (u : ℝ) (n : ℕ) : ℂ := (n : ℂ) ^ (-(Complex.I * u))

lemma pwt_norm {u : ℝ} {n : ℕ} (hn : 1 ≤ n) : ‖pwt u n‖ = 1 := by
  simp only [pwt]
  exact norm_cpow_neg_I_mul u hn

/-- The extra primes of `primesIn P (2P)` outside `(⌊P⌋₊, ⌊2P⌋₊]` contribute at most `1`. -/
lemma bound_A (P u : ℝ) :
    ‖∑ p ∈ (primesIn P (2 * P)) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime),
        pwt u p‖ ≤ 1 := by
  set S := (primesIn P (2 * P)) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime) with hS
  have hle : ∀ p ∈ S, ‖pwt u p‖ = 1 := by
    intro p hp
    rw [hS, Finset.mem_sdiff, primesIn, natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
    exact pwt_norm (le_of_lt hp.1.2.one_lt)
  calc ‖∑ p ∈ S, pwt u p‖ ≤ ∑ p ∈ S, ‖pwt u p‖ := norm_sum_le _ _
    _ = ∑ p ∈ S, (1 : ℝ) := Finset.sum_congr rfl hle
    _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 1 := by rw [hS]; exact_mod_cast primesIn_sdiff_card_le_one P

/-- The primes of `(⌊P⌋₊, ⌊2P⌋₊]` contribute at most `(#primes) · log 2 / log P`. -/
lemma bound_D (P u : ℝ) (hP : 2 ≤ P) :
    ‖∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
        (pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n))‖
      ≤ (((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime).card : ℝ)
          * (Real.log 2 / Real.log P) := by
  have hLpos : 0 < Real.log P := Real.log_pos (by linarith)
  have hterm : ∀ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
      ‖pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n)‖
        ≤ Real.log 2 / Real.log P := by
    intro n hn
    obtain ⟨hnIoc, hpr⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_Ioc] at hnIoc
    have hPn : (P : ℝ) < (n : ℝ) := by
      have h1 : P < ((⌊P⌋₊ : ℕ) : ℝ) + 1 := by
        simpa using Nat.lt_floor_add_one P
      have h2 : ((⌊P⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hnIoc.1
      push_cast at h2
      linarith
    have hn2P : (n : ℝ) ≤ 2 * P := by
      have h2 : (n : ℝ) ≤ ((⌊2 * P⌋₊ : ℕ) : ℝ) := by exact_mod_cast hnIoc.2
      have h3 : ((⌊2 * P⌋₊ : ℕ) : ℝ) ≤ 2 * P := Nat.floor_le (by linarith)
      linarith
    have hnpos : 0 < (n : ℝ) := by linarith
    have hloglt : Real.log P < Real.log n := Real.log_lt_log (by linarith) hPn
    have hlogle : Real.log n ≤ Real.log (2 * P) := Real.log_le_log hnpos hn2P
    have hlog2P : Real.log (2 * P) = Real.log 2 + Real.log P :=
      Real.log_mul (by norm_num) (by linarith)
    have hdiff : Real.log n - Real.log P ≤ Real.log 2 := by
      have h : Real.log n ≤ Real.log 2 + Real.log P := by rw [← hlog2P]; exact hlogle
      linarith
    have habs : |1 - Real.log n / Real.log P| ≤ Real.log 2 / Real.log P := by
      have hnonpos : 1 - Real.log n / Real.log P ≤ 0 := by
        rw [sub_nonpos]
        exact (one_le_div hLpos).mpr hloglt.le
      rw [abs_of_nonpos hnonpos, neg_sub, div_sub_one hLpos.ne']
      exact div_le_div_of_nonneg_right hdiff hLpos.le
    have hnorm : ‖pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n)‖
        = |1 - Real.log n / Real.log P| := by
      have hfac : pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n)
          = (((1 - Real.log n / Real.log P : ℝ)) : ℂ) * pwt u n := by
        simp only [pwt]; push_cast; ring
      rw [hfac, norm_mul, pwt_norm (le_of_lt hpr.one_lt), mul_one]
      exact RCLike.norm_ofReal _
    rw [hnorm]
    exact habs
  calc ‖∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime, _‖
      ≤ ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime, ‖_‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime, (Real.log 2 / Real.log P) :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime).card : ℝ) * (Real.log 2 / Real.log P) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The non-prime von Mangoldt mass in `(⌊P⌋₊, ⌊2P⌋₊]` is at most `2√2·√P·log(2P)`. -/
lemma bound_E (P u : ℝ) (hP : 2 ≤ P) :
    ‖(1 / Real.log P) * ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime),
        (((Λ n : ℝ) : ℂ) * pwt u n)‖
      ≤ 2 * Real.sqrt 2 * Real.sqrt P * Real.log (2 * P) / Real.log P := by
  have hLpos : 0 < Real.log P := Real.log_pos (by linarith)
  have hcast : (1 / Real.log P : ℂ) = ((1 / Real.log P : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  set B : Finset ℕ := Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊ with hB
  set D : Finset ℕ := B.filter Nat.Prime with hD
  have hnorm : ‖∑ n ∈ B \ D, (((Λ n : ℝ) : ℂ) * pwt u n)‖ ≤ ∑ n ∈ B \ D, Λ n := by
    calc ‖∑ n ∈ B \ D, (((Λ n : ℝ) : ℂ) * pwt u n)‖
        ≤ ∑ n ∈ B \ D, ‖(((Λ n : ℝ) : ℂ) * pwt u n)‖ := norm_sum_le _ _
      _ = ∑ n ∈ B \ D, Λ n := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have hnB : n ∈ B := (Finset.mem_sdiff.mp hn).1
          rw [hB, Finset.mem_Ioc] at hnB
          have hn1 : 1 ≤ n := by omega
          rw [norm_mul, pwt_norm hn1, mul_one]
          exact_mod_cast (abs_of_nonneg vonMangoldt_nonneg)
  have hsub : ∑ n ∈ B \ D, Λ n ≤ Chebyshev.psi (2 * P) - Chebyshev.theta (2 * P) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      have hnB : n ∈ B := (Finset.mem_sdiff.mp hn).1
      have hnD : n ∉ D := (Finset.mem_sdiff.mp hn).2
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Ioc]
        have h := hnB
        rw [hB, Finset.mem_Ioc] at h
        exact ⟨by omega, h.2⟩
      · rw [hD] at hnD
        intro hpr
        exact hnD (Finset.mem_filter.mpr ⟨hnB, hpr⟩)
    · intro n _ _
      exact vonMangoldt_nonneg
  have hpsitheta : Chebyshev.psi (2 * P) - Chebyshev.theta (2 * P)
      ≤ 2 * Real.sqrt (2 * P) * Real.log (2 * P) := by
    have h := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (show (1 : ℝ) ≤ 2 * P by linarith)
    linarith [le_abs_self (Chebyshev.psi (2 * P) - Chebyshev.theta (2 * P))]
  have hsqrt : Real.sqrt (2 * P) = Real.sqrt 2 * Real.sqrt P := Real.sqrt_mul (by norm_num) P
  have hpos : (0 : ℝ) < 1 / Real.log P := by rw [one_div]; exact inv_pos.mpr hLpos
  calc ‖((1 / Real.log P : ℝ) : ℂ) * ∑ n ∈ B \ D, (((Λ n : ℝ) : ℂ) * pwt u n)‖
      = (1 / Real.log P) * ‖∑ n ∈ B \ D, (((Λ n : ℝ) : ℂ) * pwt u n)‖ := by
        rw [norm_mul]
        have hc : ‖((1 / Real.log P : ℝ) : ℂ)‖ = (1 / Real.log P : ℝ) :=
          (RCLike.norm_ofReal (K := ℂ) (1 / Real.log P)).trans (abs_of_pos hpos)
        rw [hc]
    _ ≤ (1 / Real.log P) * (2 * Real.sqrt 2 * Real.sqrt P * Real.log (2 * P)) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hpos)
        calc ‖∑ n ∈ B \ D, (((Λ n : ℝ) : ℂ) * pwt u n)‖ ≤ ∑ n ∈ B \ D, Λ n := hnorm
          _ ≤ Chebyshev.psi (2 * P) - Chebyshev.theta (2 * P) := hsub
          _ ≤ 2 * Real.sqrt (2 * P) * Real.log (2 * P) := hpsitheta
          _ = 2 * Real.sqrt 2 * Real.sqrt P * Real.log (2 * P) := by rw [hsqrt]; ring
    _ = 2 * Real.sqrt 2 * Real.sqrt P * Real.log (2 * P) / Real.log P := by ring

/-- **Prime sum versus logarithmically weighted von Mangoldt sum.**
There are constants `C, P₀ > 0` such that for every real `P ≥ P₀` and every real `u`,
`‖∑_{P ≤ p ≤ 2P} p^{-iu} - (1/log P)·∑_{P < n ≤ 2P} Λ(n)·n^{-iu}‖ ≤ C·P/(log P)²`.

The left sum runs over the primes in the real interval `[P, 2P]` (`primesIn P (2*P)`),
the right one over the integers `n` with `P < n ≤ 2P` (`Finset.Ioc ⌊P⌋₊ ⌊2*P⌋₊`).
Route: on `P < n ≤ 2P` one has `Λ(n)/log n = 1` at primes and `= 1/k` at `n = p^k`
(with `Λ` vanishing at non-prime-powers), so the difference is a sum of at most one
boundary prime (the left sum may include `p = P` when `P` is an integer) plus one term
of modulus `≤ 1` per proper prime power `p^k`, `k ≥ 2`, in the range; their number is
`O(√P)` (indeed at most one power of each prime `p ≤ √(2P)` lies in the ratio-2 window
`(P,2P]`, so the count is `≤ #\{p ≤ √(2P)\} ≤ √(2P)`). The remaining error is
`Σ_{P<n≤2P} Λ(n)·|1/log n − 1/log P| ≤ (2 log 2/log²P)·ψ(2P) = O(P/log²P)`, using
the relative variation of `1/log` on `[P,2P]` and Chebyshev's bound `ψ(x) ≪ x`
(Mathlib: `Chebyshev.psi_le_const_mul_self`). Also `|n^{-iu}| = 1` for `n ≥ 1`. -/
theorem primeSum_mangoldt_le :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (P : ℝ) (u : ℝ), P₀ ≤ P →
      ‖∑ p ∈ primesIn P (2 * P), (p : ℂ) ^ (-(Complex.I * u))
        - (1 / Real.log P) * ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))‖
        ≤ C * P / (Real.log P) ^ 2 := by
  obtain ⟨P₁, _hP₁2, hP₁⟩ := log_mul_log_le_sqrt
  obtain ⟨C₂, hC₂pos, hC₂⟩ := dyadic_prime_card_le
  refine ⟨1 + C₂ * Real.log 2 + 2 * Real.sqrt 2, max P₁ 2, ?_, ?_⟩
  · have h1 : 0 < C₂ * Real.log 2 := mul_pos hC₂pos (Real.log_pos one_lt_two)
    have h2 : 0 < 2 * Real.sqrt 2 := by positivity
    linarith
  · intro P u hP
    have hPP₁ : P₁ ≤ P := le_trans (le_max_left _ _) hP
    have hP2 : 2 ≤ P := le_trans (le_max_right _ _) hP
    have hPpos : 0 < P := by linarith
    have hLpos : 0 < Real.log P := Real.log_pos (by linarith)
    have hAn : Real.log P * Real.log (2 * P) ≤ Real.sqrt P := hP₁ P hPP₁
    have hlog2Pge : Real.log P ≤ Real.log (2 * P) := Real.log_le_log (by linarith) (by linarith)
    -- `1 ≤ P / (log P)^2`
    have hQ1 : 1 ≤ P / (Real.log P) ^ 2 := by
      have h1 : (Real.log P) ^ 2 ≤ Real.log P * Real.log (2 * P) := by nlinarith [hLpos, hlog2Pge]
      have h2 : Real.sqrt P ≤ P := (Real.sqrt_le_left (le_of_lt hPpos)).mpr (by nlinarith [hP2])
      have h3 : (Real.log P) ^ 2 ≤ P := le_trans h1 (le_trans hAn h2)
      rw [one_le_div (by positivity)]
      exact h3
    have hbA : ‖∑ p ∈ (primesIn P (2 * P)) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime),
        pwt u p‖ ≤ 1 := bound_A P u
    have hbD0 := bound_D P u hP2
    have hcard : (((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime).card : ℝ)
        ≤ C₂ * P / Real.log P := hC₂ P hP2
    have hbD : ‖∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
        (pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n))‖
        ≤ C₂ * Real.log 2 * P / (Real.log P) ^ 2 := by
      calc ‖∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime, _‖
          ≤ (((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime).card : ℝ)
              * (Real.log 2 / Real.log P) := hbD0
        _ ≤ (C₂ * P / Real.log P) * (Real.log 2 / Real.log P) :=
              mul_le_mul_of_nonneg_right hcard (div_nonneg (Real.log_nonneg one_le_two) hLpos.le)
        _ = C₂ * Real.log 2 * P / (Real.log P) ^ 2 := by ring
    have hdiv : Real.sqrt P * Real.log (2 * P) ≤ P / Real.log P := by
      rw [le_div_iff₀ hLpos]
      calc Real.sqrt P * Real.log (2 * P) * Real.log P
          = Real.sqrt P * (Real.log P * Real.log (2 * P)) := by ring
        _ ≤ Real.sqrt P * Real.sqrt P := mul_le_mul_of_nonneg_left hAn (Real.sqrt_nonneg P)
        _ = P := by rw [Real.mul_self_sqrt (le_of_lt hPpos)]
    have hthird : 2 * Real.sqrt 2 * Real.sqrt P * Real.log (2 * P) / Real.log P
        ≤ 2 * Real.sqrt 2 * (P / (Real.log P) ^ 2) := by
      have hdiv2 : Real.sqrt P * Real.log (2 * P) / Real.log P
          ≤ P / (Real.log P) ^ 2 := by
        have h := div_le_div_of_nonneg_right hdiv hLpos.le
        rw [div_div, ← sq] at h
        exact h
      calc 2 * Real.sqrt 2 * Real.sqrt P * Real.log (2 * P) / Real.log P
          = 2 * Real.sqrt 2 * (Real.sqrt P * Real.log (2 * P) / Real.log P) := by ring
        _ ≤ 2 * Real.sqrt 2 * (P / (Real.log P) ^ 2) :=
            mul_le_mul_of_nonneg_left hdiv2 (by positivity)
    have hbE : ‖(1 / Real.log P) * ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime),
        (((Λ n : ℝ) : ℂ) * pwt u n)‖ ≤ 2 * Real.sqrt 2 * (P / (Real.log P) ^ 2) :=
      le_trans (bound_E P u hP2) hthird
    -- assemble
    have hDsubA : (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime ⊆ primesIn P (2 * P) :=
      Ioc_filter_prime_subset_primesIn P
    have hDsubB : (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime ⊆ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊ :=
      Finset.filter_subset _ _
    have hDcongr :
        ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime, (((Λ n : ℝ) : ℂ) * pwt u n)
        = ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime, (((Real.log n : ℝ) : ℂ) * pwt u n) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      obtain ⟨_, hpr⟩ := Finset.mem_filter.mp hn
      rw [vonMangoldt_apply_prime hpr]
    have hmulD :
        ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime, pwt u n
          - (1 / Real.log P) * ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
              (((Real.log n : ℝ) : ℂ) * pwt u n)
        = ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
              (pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have key : ∑ p ∈ primesIn P (2 * P), pwt u p
          - (1 / Real.log P) * ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊, (((Λ n : ℝ) : ℂ) * pwt u n)
        = ∑ p ∈ (primesIn P (2 * P)) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime), pwt u p
          + ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
              (pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n))
          - (1 / Real.log P) * ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime),
              (((Λ n : ℝ) : ℂ) * pwt u n) := by
      rw [← Finset.sum_sdiff hDsubA, ← Finset.sum_sdiff hDsubB, hDcongr, ← hmulD]
      ring
    change ‖∑ p ∈ primesIn P (2 * P), pwt u p
        - (1 / Real.log P) * ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * pwt u n‖
        ≤ (1 + C₂ * Real.log 2 + 2 * Real.sqrt 2) * P / (Real.log P) ^ 2
    rw [key]
    have htri : ‖∑ p ∈ (primesIn P (2 * P)) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime), pwt u p
          + ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
              (pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n))
          - (1 / Real.log P) * ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime),
              (((Λ n : ℝ) : ℂ) * pwt u n)‖
        ≤ 1 + C₂ * Real.log 2 * P / (Real.log P) ^ 2
            + 2 * Real.sqrt 2 * (P / (Real.log P) ^ 2) := by
      calc ‖∑ p ∈ (primesIn P (2 * P)) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime), pwt u p
            + ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
                (pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n))
            - (1 / Real.log P) * ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime),
                (((Λ n : ℝ) : ℂ) * pwt u n)‖
          ≤ ‖∑ p ∈ (primesIn P (2 * P)) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime), pwt u p
              + ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
                  (pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n))‖
            + ‖(1 / Real.log P) * ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime),
                (((Λ n : ℝ) : ℂ) * pwt u n)‖ :=
              norm_sub_le _ _
        _ ≤ (‖∑ p ∈ (primesIn P (2 * P)) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime), pwt u p‖
              + ‖∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime,
                  (pwt u n - (1 / Real.log P) * (((Real.log n : ℝ) : ℂ) * pwt u n))‖)
            + ‖(1 / Real.log P) * ∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊) \ ((Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime),
                (((Λ n : ℝ) : ℂ) * pwt u n)‖ := by
              gcongr
              exact norm_add_le _ _
        _ ≤ 1 + C₂ * Real.log 2 * P / (Real.log P) ^ 2
            + 2 * Real.sqrt 2 * (P / (Real.log P) ^ 2) := by
              linarith [hbA, hbD, hbE]
    refine le_trans htri ?_
    calc 1 + C₂ * Real.log 2 * P / (Real.log P) ^ 2 + 2 * Real.sqrt 2 * (P / (Real.log P) ^ 2)
        = 1 + (C₂ * Real.log 2 + 2 * Real.sqrt 2) * (P / (Real.log P) ^ 2) := by ring
      _ ≤ P / (Real.log P) ^ 2 + (C₂ * Real.log 2 + 2 * Real.sqrt 2) * (P / (Real.log P) ^ 2) := by
          nlinarith [hQ1]
      _ = (1 + C₂ * Real.log 2 + 2 * Real.sqrt 2) * P / (Real.log P) ^ 2 := by ring

end Work.BMF
