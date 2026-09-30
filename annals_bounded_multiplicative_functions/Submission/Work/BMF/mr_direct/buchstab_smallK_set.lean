import Mathlib
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.card_has_prime_factorR_le
import Submission.Work.BMF.mr_direct.goodSet_bound_range_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The `K log(Q/P) < 1` (count-only) case of the range Buchstab/Ramaré bound of
Matomäki–Radziwiłł, Lemma `lem:decomp`, for the integral over a measurable set `u ⊆ [-S,S]`:
for `a` vanishing on the integers having no prime factor in `[P,Q]`, the mean square of
`dirPolyR a X₁ X₂` over `u` is bounded by the trivial term only (the term
`(S+X₂)/X₁·(1/K+1/P)` of the decomposition).

This is the general-range, set-integral version of the second case of the proof of
`Work.BMF.mr_direct.buchstab_range` (read that file for the template, whose `Case B` branch is
exactly this argument): use the mean value theorem
`Work.BMF.mrDirect.MVConst.mv_natIcc` together with `∫_u ≤ ∫_{(-S)..S}` for nonnegative
integrands (`setIntegral_le_intervalIntegral` in `goodSet_bound_range_defs.lean`), restrict to the
integers having a prime factor in `[P,Q]` via the support hypothesis, bound their number by
`card_has_prime_factorR_le`, and finish with the arithmetic
`12 * (X₂/X₁) * (2S+3C₀X₂) ≤ 10000000 * (C₀+1) * (S+X₂)`. -/
theorem buchstab_smallK_set (C₀ : ℝ) (hC₀ : Work.BMF.mrDirect.MVConst C₀)
    (a b c : ℕ → ℂ) (X₁ X₂ K P Q S : ℝ) (u : Set ℝ)
    (hX1 : 1 ≤ X₁) (hX12 : X₁ ≤ X₂) (hX24 : X₂ ≤ 4 * X₁)
    (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q) (hS : 0 ≤ S)
    (hasupp : ∀ n : ℕ, (∀ p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ n) →
      a n = 0)
    (hmul : ∀ m p : ℕ, Nat.Prime p → P ≤ (p : ℝ) → (p : ℝ) ≤ Q → ¬ p ∣ m →
      a (m * p) = b m * c p)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hu : MeasurableSet u) (husub : u ⊆ Set.Icc (-S) S)
    (hsmall : K * Real.log (Q / P) < 1) :
    (∫ t in u, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ 10000000 * (C₀ + 1) * ((S + X₂) / X₁ * (1 / K + 1 / P)) := by
  have hX1pos : 0 < X₁ := lt_of_lt_of_le zero_lt_one hX1
  have hX2nn : (0 : ℝ) ≤ X₂ := le_trans hX1pos.le hX12
  have hX21 : 1 ≤ X₂ := le_trans hX1 hX12
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hPpos : 0 < P := by linarith
  have hCnn : 0 ≤ C₀ := Work.BMF.mrDirect.MVConst.nonneg hC₀
  have hcoefnn : 0 ≤ 2 * S + 3 * C₀ * X₂ := by nlinarith [hCnn, hS, hX2nn]
  -- Step 1: pass from the set integral to the interval integral.
  have hcont : Continuous fun t : ℝ => ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2 :=
    ((Work.BMF.mrDirect.continuous_dirPolyR a X₁ X₂ hX1pos).norm.pow 2)
  have hle_int : (∫ t in u, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ (∫ t in (-S)..S, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2) :=
    setIntegral_le_intervalIntegral hS husub hcont (fun x _ => by positivity)
  -- Step 2: the mean value (large sieve) bound.
  have hMV : (∫ t in (-S)..S, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * X₂) * ∑ n ∈ Work.BMF.natIcc X₁ X₂, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
    hC₀.mv_natIcc a X₁ X₂ S hX1pos hX12 hS
  -- Step 3: `a` is supported on the integers having a prime factor in `[P,Q]`.
  have hsupp : ∀ n ∈ Work.BMF.natIcc X₁ X₂, a n ≠ 0 →
      ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n := by
    intro n _ hane
    by_contra hcon
    exact hane (hasupp n (fun p hpp hPp hpQ hpd =>
      hcon ⟨p, Work.BMF.mrDirect.mem_primeSet' hpp hPp hpQ, hpd⟩))
  -- Step 4: count-only bound for the coefficient energy.
  have hsum_le : (∑ n ∈ Work.BMF.natIcc X₁ X₂, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ 12 * X₂ * (1 / K + 1 / P) * (1 / X₁ ^ 2) := by
    have h1 : (∑ n ∈ Work.BMF.natIcc X₁ X₂, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
        = ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter (fun n => a n ≠ 0),
            ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases h : a n = 0 <;> simp [h]
    rw [h1]
    have hsub : (Work.BMF.natIcc X₁ X₂).filter (fun n => a n ≠ 0)
        ⊆ (Work.BMF.natIcc X₁ X₂).filter
            (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n) := by
      intro n hn
      obtain ⟨hnN, hane⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hnN, hsupp n hnN hane⟩
    have hstep1 : ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter (fun n => a n ≠ 0),
          ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
            (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n), ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro n hnN hnotin
      have hz : a n = 0 := by
        by_contra h
        exact hnotin (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnN).1, h⟩)
      simp [hz]
    have hstep2 : ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
            (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n), ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ ∑ _n ∈ (Work.BMF.natIcc X₁ X₂).filter
            (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n), 1 / X₁ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnN, -⟩ := Finset.mem_filter.mp hn
      rw [Work.BMF.natIcc, Finset.mem_Icc] at hnN
      have hnlo : X₁ ≤ (n : ℝ) := le_trans (Nat.le_ceil X₁) (by exact_mod_cast hnN.1)
      have hb1 : ‖a n‖ ^ 2 ≤ 1 := by
        have := ha n
        nlinarith [norm_nonneg (a n)]
      calc ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hb1 (by positivity)
        _ ≤ 1 / X₁ ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hstep3 : ∑ _n ∈ (Work.BMF.natIcc X₁ X₂).filter
            (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n), 1 / X₁ ^ 2
        = (((Work.BMF.natIcc X₁ X₂).filter
            (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n)).card : ℝ)
            * (1 / X₁ ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcard' : (((Work.BMF.natIcc X₁ X₂).filter
          (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n)).card : ℝ)
        ≤ 12 * X₂ * (1 / K + 1 / P) :=
      card_has_prime_factorR_le X₁ X₂ K P Q hX1 hX21 hK hP hPQ hsmall
    calc ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter (fun n => a n ≠ 0),
          ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
            (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n), ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
          hstep1
      _ ≤ ∑ _n ∈ (Work.BMF.natIcc X₁ X₂).filter
            (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n), 1 / X₁ ^ 2 := hstep2
      _ = (((Work.BMF.natIcc X₁ X₂).filter
            (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n)).card : ℝ)
            * (1 / X₁ ^ 2) := hstep3
      _ ≤ (12 * X₂ * (1 / K + 1 / P)) * (1 / X₁ ^ 2) :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
  -- Step 5: arithmetic.
  have hfin : (2 * S + 3 * C₀ * X₂) * (12 * X₂ * (1 / K + 1 / P) * (1 / X₁ ^ 2))
      ≤ 10000000 * (C₀ + 1) * ((S + X₂) / X₁ * (1 / K + 1 / P)) := by
    have hratio : X₂ / X₁ ≤ 4 := by
      rw [div_le_iff₀ hX1pos]
      linarith [hX24]
    have hkey : 12 * (X₂ / X₁) * (2 * S + 3 * C₀ * X₂)
        ≤ 10000000 * (C₀ + 1) * (S + X₂) := by
      have h3 : 12 * (X₂ / X₁) * (2 * S + 3 * C₀ * X₂) ≤ 48 * (2 * S + 3 * C₀ * X₂) := by
        nlinarith [hratio, hcoefnn]
      have h4 : 48 * (2 * S + 3 * C₀ * X₂) ≤ 48 * (3 * (C₀ + 1) * (S + X₂)) := by
        have h5 : 2 * S + 3 * C₀ * X₂ ≤ 3 * (C₀ + 1) * (S + X₂) := by
          nlinarith [hCnn, hS, hX2nn]
        linarith
      have h6 : 48 * (3 * (C₀ + 1) * (S + X₂)) ≤ 10000000 * (C₀ + 1) * (S + X₂) := by
        have h7 : (48 : ℝ) * 3 ≤ 10000000 := by norm_num
        have h8 : (48 : ℝ) * 3 * ((C₀ + 1) * (S + X₂)) ≤ 10000000 * ((C₀ + 1) * (S + X₂)) :=
          mul_le_mul_of_nonneg_right h7 (by positivity)
        linarith [h8]
      linarith [h3, h4, h6]
    have hfac : 12 * X₂ * (1 / K + 1 / P) * (1 / X₁ ^ 2)
        = (12 * (X₂ / X₁)) * ((1 / K + 1 / P) / X₁) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hfac]
    calc (2 * S + 3 * C₀ * X₂) * (12 * (X₂ / X₁) * ((1 / K + 1 / P) / X₁))
        = (12 * (X₂ / X₁) * (2 * S + 3 * C₀ * X₂)) * ((1 / K + 1 / P) / X₁) := by ring
      _ ≤ (10000000 * (C₀ + 1) * (S + X₂)) * ((1 / K + 1 / P) / X₁) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = 10000000 * (C₀ + 1) * ((S + X₂) / X₁ * (1 / K + 1 / P)) := by ring
  calc (∫ t in u, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2)
      ≤ (∫ t in (-S)..S, ‖Work.BMF.mrDirect.dirPolyR a X₁ X₂ t‖ ^ 2) := hle_int
    _ ≤ (2 * S + 3 * C₀ * X₂) * ∑ n ∈ Work.BMF.natIcc X₁ X₂, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := hMV
    _ ≤ (2 * S + 3 * C₀ * X₂) * (12 * X₂ * (1 / K + 1 / P) * (1 / X₁ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum_le hcoefnn
    _ ≤ 10000000 * (C₀ + 1) * ((S + X₂) / X₁ * (1 / K + 1 / P)) := hfin

end Work.BMF.mr_direct
