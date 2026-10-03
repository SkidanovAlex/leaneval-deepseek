import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_prep
import Submission.Work.KMTAreas.A7.varphitildeNt_eq_profile
import Submission.Work.KMTAreas.A7.kmtEta_deriv_bounds

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open Finset Polynomial
open scoped BigOperators

noncomputable section

/-! ## The case `d = 0` of the Mikhlin bound for the randomised `g`-side symbol -/

/-! ## The case `d = 0` -/

/-- **The `d = 0` case.**  Here `P` is constant and `gProfile 0 k₂` is either `η` or `0`, so the
symbol is a single modulated bump times a bounded coefficient. -/
theorem rSG_d0 (P : Polynomial ℤ) (hd0 : P.natDegree ≤ 0) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (K : ℕ) (c : ℕ → ℂ) (hc : ∀ u v : ℕ, ‖∑ m ∈ Finset.Icc u v, c m‖ ≤ 4),
        MikhlinBound (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1),
            c m * varphitildeNt P 0 (Nat.floor (a m)) k₂ t ξ)
          (C * (1 + (2 : ℝ) ^ (0 * k₂)) ^ 2) := by
  classical
  obtain ⟨Q0, Q1, Q2, hQ0nn, hQ1nn, hQ2nn, -, hQ0, hQ1, hQ2, hz0, hz1, hz2, hQd1, hQd2⟩ :=
    kmtEta_deriv_bounds
  have hQ0all : ∀ y : ℝ, ‖Work.KMTContract.kmtEta y‖ ≤ Q0 := by
    intro y
    by_cases h : |y| ≤ 1
    · exact hQ0 y h
    · rw [hz0 y (le_of_lt (not_le.mp h)), norm_zero]; exact hQ0nn
  have hQ1all : ∀ y : ℝ, ‖deriv Work.KMTContract.kmtEta y‖ ≤ Q1 := by
    intro y
    by_cases h : |y| ≤ 1
    · exact hQ1 y h
    · rw [hz1 y (le_of_lt (not_le.mp h)), norm_zero]; exact hQ1nn
  have hQ2all : ∀ y : ℝ, ‖iteratedDeriv 2 Work.KMTContract.kmtEta y‖ ≤ Q2 := by
    intro y
    by_cases h : |y| ≤ 1
    · exact hQ2 y h
    · rw [hz2 y (le_of_lt (not_le.mp h)), norm_zero]; exact hQ2nn
  set q : ℝ := ((P.coeff 0 : ℤ) : ℝ) with hq
  have hq0 : ∀ x : ℝ, PevalR P x = q := by
    intro x
    have hP : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hd0
    rw [PevalR, hP, Polynomial.map_C, Polynomial.eval_C, hq]
    rfl
  have hgscale : ∀ (k₂ N : ℕ), gScale 0 N k₂ = 1 := by
    intro k₂ N
    show (2 : ℝ) ^ ((0 : ℤ) * (Work.Analysis.EndVar.logN N - (k₂ : ℤ))) = 1
    rw [zero_mul]
    exact zpow_zero 2
  have hgprof : ∀ k₂ : ℕ, gProfile 0 k₂ = (if k₂ = 0 then Work.KMTContract.kmtEta else 0) := by
    intro k₂
    by_cases hk : k₂ = 0
    · rw [gProfile, if_pos hk, if_pos hk]
    · rw [gProfile, if_neg hk, if_neg hk]
      funext u
      show Work.KMTContract.kmtEta u - Work.KMTContract.kmtEta ((2 : ℝ) ^ 0 * u) = 0
      rw [pow_zero, one_mul, sub_self]
  set QS : ℝ := Q0 + Q1 + Q2 + 1 with hQS
  have hQSnn : 0 ≤ QS := by rw [hQS]; linarith
  set C0 : ℝ := QS * (|q| + 1) ^ 2 * 10000 with hC0
  have hC0nn : 0 ≤ C0 := by
    rw [hC0]
    exact mul_nonneg (mul_nonneg hQSnn (by positivity)) (by norm_num)
  have habs1 : (1 : ℝ) ≤ (|q| + 1) ^ 2 := by nlinarith [abs_nonneg q]
  have hbig1 : (1 : ℝ) ≤ (|q| + 1) ^ 2 * 10000 := by nlinarith [habs1]
  have hQ0C : Q0 ≤ C0 := by
    rw [hC0, hQS]
    have h0 : (0 : ℝ) ≤ Q0 + Q1 + Q2 + 1 := by linarith
    calc Q0 ≤ Q0 + Q1 + Q2 + 1 := by linarith
      _ = (Q0 + Q1 + Q2 + 1) * 1 := (mul_one _).symm
      _ ≤ (Q0 + Q1 + Q2 + 1) * ((|q| + 1) ^ 2 * 10000) := mul_le_mul_of_nonneg_left hbig1 h0
      _ = (Q0 + Q1 + Q2 + 1) * (|q| + 1) ^ 2 * 10000 := by ring
  have hfacg : ∀ (c a b B : ℝ), 0 ≤ c → c ≤ 100 → 0 ≤ a → a ≤ QS → 0 ≤ b →
      b ≤ (|q| + 1) ^ 2 → 1 ≤ 100 * B → c * a * b ≤ C0 * B := by
    intro c a b B hc0 hc ha0 ha hb0 hb hB
    have h2 : a * b ≤ QS * (|q| + 1) ^ 2 := mul_le_mul ha hb hb0 hQSnn
    have h1 : c * a * b ≤ 100 * (QS * (|q| + 1) ^ 2) := by
      calc c * a * b = (a * b) * c := by ring
        _ ≤ QS * (|q| + 1) ^ 2 * 100 := mul_le_mul h2 hc hc0 (by positivity)
        _ = 100 * (QS * (|q| + 1) ^ 2) := by ring
    have hK : (0 : ℝ) ≤ QS * (|q| + 1) ^ 2 := mul_nonneg hQSnn (by positivity)
    have h3 : 100 * (QS * (|q| + 1) ^ 2) ≤ C0 * B := by
      rw [hC0]
      nlinarith [hK, hB]
    linarith
  have hQ0q : Q0 ≤ C0 / 4 := by
    have h := hfacg 1 Q0 1 (1 / 4) (by norm_num) (by norm_num) hQ0nn
      (by rw [hQS]; linarith) (by norm_num) (by nlinarith [habs1]) (by norm_num)
    linarith [h]
  have hQ1q : Q1 ≤ C0 / 4 := by
    have h := hfacg 1 Q1 1 (1 / 4) (by norm_num) (by norm_num) hQ1nn
      (by rw [hQS]; linarith) (by norm_num) (by nlinarith [habs1]) (by norm_num)
    linarith [h]
  have hQ2q : Q2 ≤ C0 / 4 := by
    have h := hfacg 1 Q2 1 (1 / 4) (by norm_num) (by norm_num) hQ2nn
      (by rw [hQS]; linarith) (by norm_num) (by nlinarith [habs1]) (by norm_num)
    linarith [h]
  have hpia : 2 * Real.pi ≤ 100 := by linarith [Real.pi_le_four]
  have hpib : 4 * Real.pi ≤ 100 := by linarith [Real.pi_le_four]
  have hpic : 4 * Real.pi ^ 2 ≤ 100 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  have habsb : |q| ≤ (|q| + 1) ^ 2 := by nlinarith [abs_nonneg q]
  have habs2 : |q| ^ 2 ≤ (|q| + 1) ^ 2 := by nlinarith [abs_nonneg q]
  have hQ0c : Q0 ≤ QS := by rw [hQS]; linarith
  have hQ1c : Q1 ≤ QS := by rw [hQS]; linarith
  have hQ1C : Q1 + 2 * Real.pi * |q| * Q0 ≤ C0 := by
    have h2 : 2 * Real.pi * |q| * Q0 ≤ C0 / 2 := by
      have h := hfacg (2 * Real.pi) Q0 |q| (1 / 2) (by positivity) hpia hQ0nn hQ0c
        (abs_nonneg q) habsb (by norm_num)
      have he : 2 * Real.pi * Q0 * |q| = 2 * Real.pi * |q| * Q0 := by ring
      rw [he] at h
      linarith [h]
    linarith
  have hQ2C : Q2 + 4 * Real.pi * |q| * Q1 + 4 * Real.pi ^ 2 * |q| ^ 2 * Q0 ≤ C0 := by
    have h2 : 4 * Real.pi * |q| * Q1 ≤ C0 / 4 := by
      have h := hfacg (4 * Real.pi) Q1 |q| (1 / 4) (by positivity) hpib hQ1nn hQ1c
        (abs_nonneg q) habsb (by norm_num)
      have he : 4 * Real.pi * Q1 * |q| = 4 * Real.pi * |q| * Q1 := by ring
      rw [he] at h
      linarith [h]
    have h3 : 4 * Real.pi ^ 2 * |q| ^ 2 * Q0 ≤ C0 / 2 := by
      have h := hfacg (4 * Real.pi ^ 2) Q0 (|q| ^ 2) (1 / 2) (by positivity) hpic hQ0nn
        hQ0c (by positivity) habs2 (by norm_num)
      have he : 4 * Real.pi ^ 2 * Q0 * |q| ^ 2 = 4 * Real.pi ^ 2 * |q| ^ 2 * Q0 := by ring
      rw [he] at h
      linarith [h]
    linarith
  have hder1 : ∀ ξ : ℝ, deriv (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ
      = (deriv Work.KMTContract.kmtEta ξ
          + (2 * Real.pi * Complex.I * (q : ℂ)) * Work.KMTContract.kmtEta ξ) * ee (q * ξ) := by
    intro ξ
    have h := (rSG_deriv_modulatedBump_p (g := Work.KMTContract.kmtEta) hQd1 hQd2 (1 : ℝ) q).2.2.1 ξ
    simpa using h
  have hder2 : ∀ ξ : ℝ, iteratedDeriv 2 (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ
      = ((1 : ℂ) ^ 2 * iteratedDeriv 2 Work.KMTContract.kmtEta ξ
          + 2 * (2 * Real.pi * Complex.I * (q : ℂ)) * ((1 : ℂ) * deriv Work.KMTContract.kmtEta ξ)
          + (2 * Real.pi * Complex.I * (q : ℂ)) ^ 2 * Work.KMTContract.kmtEta ξ) * ee (q * ξ) := by
    intro ξ
    have h := (rSG_deriv_modulatedBump_p (g := Work.KMTContract.kmtEta) hQd1 hQd2 (1 : ℝ) q).2.2.2 ξ
    simpa using h
  have hF0 : ∀ ξ : ℝ, ‖Work.KMTContract.kmtEta ξ * ee (q * ξ)‖ ≤ Q0 := by
    intro ξ; rw [norm_mul, rSG_norm_ee, mul_one]; exact hQ0all ξ
  have hF1 : ∀ ξ : ℝ, |ξ| * ‖deriv (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ‖
      ≤ Q1 + 2 * Real.pi * |q| * Q0 := by
    intro ξ
    by_cases hξ : |ξ| ≤ 1
    · rw [hder1 ξ, norm_mul, rSG_norm_ee, mul_one]
      have h1 : ‖deriv Work.KMTContract.kmtEta ξ‖ ≤ Q1 := hQ1all ξ
      have h2 : ‖(2 * Real.pi * Complex.I * (q : ℂ)) * Work.KMTContract.kmtEta ξ‖
          ≤ 2 * Real.pi * |q| * Q0 := by
        rw [norm_mul, rSG_norm_two_pi_I_mul]
        exact mul_le_mul_of_nonneg_left (hQ0all ξ) (by positivity)
      have h3 : ‖deriv Work.KMTContract.kmtEta ξ
            + (2 * Real.pi * Complex.I * (q : ℂ)) * Work.KMTContract.kmtEta ξ‖
          ≤ Q1 + 2 * Real.pi * |q| * Q0 := (norm_add_le _ _).trans (add_le_add h1 h2)
      calc |ξ| * ‖deriv Work.KMTContract.kmtEta ξ
            + (2 * Real.pi * Complex.I * (q : ℂ)) * Work.KMTContract.kmtEta ξ‖
          ≤ |ξ| * (Q1 + 2 * Real.pi * |q| * Q0) :=
            mul_le_mul_of_nonneg_left h3 (abs_nonneg ξ)
        _ ≤ 1 * (Q1 + 2 * Real.pi * |q| * Q0) := mul_le_mul_of_nonneg_right hξ (by positivity)
        _ = Q1 + 2 * Real.pi * |q| * Q0 := one_mul _
    · have hξ1 : 1 < |ξ| := not_le.mp hξ
      have hz : deriv (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ = 0 := by
        rw [hder1 ξ, hz0 ξ (le_of_lt hξ1), hz1 ξ (le_of_lt hξ1)]
        ring
      rw [hz, norm_zero, mul_zero]
      have hB : 0 ≤ Q1 + 2 * Real.pi * |q| * Q0 := by positivity
      linarith
  have hF2 : ∀ ξ : ℝ, |ξ| ^ 2
      * ‖iteratedDeriv 2 (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ‖
      ≤ Q2 + 4 * Real.pi * |q| * Q1 + 4 * Real.pi ^ 2 * |q| ^ 2 * Q0 := by
    intro ξ
    by_cases hξ : |ξ| ≤ 1
    · rw [hder2 ξ, norm_mul, rSG_norm_ee, mul_one]
      have h1 : ‖(1 : ℂ) ^ 2 * iteratedDeriv 2 Work.KMTContract.kmtEta ξ‖ ≤ Q2 := by
        rw [one_pow, one_mul]; exact hQ2all ξ
      have h2 : ‖2 * (2 * Real.pi * Complex.I * (q : ℂ)) * ((1 : ℂ) * deriv Work.KMTContract.kmtEta ξ)‖
          ≤ 4 * Real.pi * |q| * Q1 := by
        rw [one_mul, norm_mul, norm_mul, rSG_norm_two_pi_I_mul]
        have h4 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h4]
        have hp : 0 ≤ 2 * (2 * Real.pi * |q|) := by positivity
        calc 2 * (2 * Real.pi * |q|) * ‖deriv Work.KMTContract.kmtEta ξ‖
            ≤ 2 * (2 * Real.pi * |q|) * Q1 :=
              mul_le_mul_of_nonneg_left (hQ1all ξ) hp
          _ = 4 * Real.pi * |q| * Q1 := by ring
      have h3 : ‖(2 * Real.pi * Complex.I * (q : ℂ)) ^ 2 * Work.KMTContract.kmtEta ξ‖
          ≤ 4 * Real.pi ^ 2 * |q| ^ 2 * Q0 := by
        rw [norm_mul, norm_pow, rSG_norm_two_pi_I_mul]
        calc (2 * Real.pi * |q|) ^ 2 * ‖Work.KMTContract.kmtEta ξ‖
            ≤ (2 * Real.pi * |q|) ^ 2 * Q0 :=
              mul_le_mul_of_nonneg_left (hQ0all ξ) (by positivity)
          _ = 4 * Real.pi ^ 2 * |q| ^ 2 * Q0 := by ring
      have h4 : ‖(1 : ℂ) ^ 2 * iteratedDeriv 2 Work.KMTContract.kmtEta ξ
            + 2 * (2 * Real.pi * Complex.I * (q : ℂ)) * ((1 : ℂ) * deriv Work.KMTContract.kmtEta ξ)
            + (2 * Real.pi * Complex.I * (q : ℂ)) ^ 2 * Work.KMTContract.kmtEta ξ‖
          ≤ Q2 + 4 * Real.pi * |q| * Q1 + 4 * Real.pi ^ 2 * |q| ^ 2 * Q0 :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)
      calc |ξ| ^ 2 * ‖(1 : ℂ) ^ 2 * iteratedDeriv 2 Work.KMTContract.kmtEta ξ
            + 2 * (2 * Real.pi * Complex.I * (q : ℂ)) * ((1 : ℂ) * deriv Work.KMTContract.kmtEta ξ)
            + (2 * Real.pi * Complex.I * (q : ℂ)) ^ 2 * Work.KMTContract.kmtEta ξ‖
          ≤ |ξ| ^ 2 * (Q2 + 4 * Real.pi * |q| * Q1 + 4 * Real.pi ^ 2 * |q| ^ 2 * Q0) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ ≤ 1 * (Q2 + 4 * Real.pi * |q| * Q1 + 4 * Real.pi ^ 2 * |q| ^ 2 * Q0) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            nlinarith [abs_nonneg ξ, hξ]
        _ = Q2 + 4 * Real.pi * |q| * Q1 + 4 * Real.pi ^ 2 * |q| ^ 2 * Q0 := one_mul _
    · have hξ1 : 1 < |ξ| := not_le.mp hξ
      have hz : iteratedDeriv 2 (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ = 0 := by
        rw [hder2 ξ, hz2 ξ (le_of_lt hξ1), hz1 ξ (le_of_lt hξ1), hz0 ξ (le_of_lt hξ1)]
        ring
      rw [hz, norm_zero, mul_zero]
      have hB : 0 ≤ Q2 + 4 * Real.pi * |q| * Q1 + 4 * Real.pi ^ 2 * |q| ^ 2 * Q0 := by positivity
      linarith
  refine ⟨C0 * 4, by positivity, ?_⟩
  intro k₂ t ht a ha ha1 K c hc
  have hpt : ∀ (m : ℕ) (x : ℝ), varphitildeNt P 0 (Nat.floor (a m)) k₂ t x
      = (if k₂ = 0 then Work.KMTContract.kmtEta x else 0) * ee (q * x) := by
    intro m x
    rw [varphitildeNt_eq_profile]
    have h1 : gScale 0 (Nat.floor (a m)) k₂ = 1 := hgscale k₂ _
    have h2 : PevalR P ((Nat.floor (a m) : ℝ) * t) = q := hq0 _
    simp only [h1, h2, one_mul, hgprof k₂]
    split_ifs with hk <;> rfl
  have hsymbol : (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1),
        c m * varphitildeNt P 0 (Nat.floor (a m)) k₂ t ξ)
      = fun ξ : ℝ => (∑ m ∈ Finset.range (K + 1), c m)
          * ((if k₂ = 0 then Work.KMTContract.kmtEta ξ else 0) * ee (q * ξ)) := by
    funext ξ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hpt m ξ]
  have hrangeIcc : ∀ v : ℕ, Finset.range (v + 1) = Finset.Icc 0 v := by
    intro v
    ext m
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  have hS4 : ‖∑ m ∈ Finset.range (K + 1), c m‖ ≤ 4 := by
    simpa [hrangeIcc K] using hc 0 K
  have hconst : (1 + (2 : ℝ) ^ (0 * k₂)) ^ 2 = 4 := by norm_num
  rw [hconst]
  by_cases hk : k₂ = 0
  · have hs : (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1),
          c m * varphitildeNt P 0 (Nat.floor (a m)) k₂ t ξ)
        = fun ξ : ℝ => (∑ m ∈ Finset.range (K + 1), c m)
            * (Work.KMTContract.kmtEta ξ * ee (q * ξ)) := by
      rw [hsymbol]
      funext ξ
      rw [if_pos hk]
    rw [hs]
    refine ⟨by positivity, ?_, ?_, ?_⟩
    · intro ξ
      rw [norm_mul, norm_mul, rSG_norm_ee, mul_one]
      calc ‖∑ m ∈ Finset.range (K + 1), c m‖ * ‖Work.KMTContract.kmtEta ξ‖ ≤ 4 * Q0 :=
            mul_le_mul hS4 (hQ0all ξ) (norm_nonneg _) (by norm_num)
        _ ≤ C0 * 4 * 4 := by linarith [hQ0C, hC0nn]
    · intro ξ
      have hdf : deriv (fun x : ℝ => (∑ m ∈ Finset.range (K + 1), c m)
            * (Work.KMTContract.kmtEta x * ee (q * x))) ξ
          = (∑ m ∈ Finset.range (K + 1), c m)
            * deriv (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ :=
        deriv_const_mul_field _
      rw [hdf, norm_mul]
      calc |ξ| * (‖∑ m ∈ Finset.range (K + 1), c m‖
            * ‖deriv (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ‖)
          = ‖∑ m ∈ Finset.range (K + 1), c m‖
            * (|ξ| * ‖deriv (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ‖) := by ring
        _ ≤ 4 * (Q1 + 2 * Real.pi * |q| * Q0) :=
            mul_le_mul hS4 (hF1 ξ) (by positivity) (by norm_num)
        _ ≤ C0 * 4 * 4 := by linarith [hQ1C, hC0nn]
    · intro ξ
      have hdd : iteratedDeriv 2 (fun x : ℝ => (∑ m ∈ Finset.range (K + 1), c m)
            * (Work.KMTContract.kmtEta x * ee (q * x))) ξ
          = (∑ m ∈ Finset.range (K + 1), c m)
            * iteratedDeriv 2 (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ :=
        iteratedDeriv_const_mul_field _ _
      rw [hdd, norm_mul]
      calc |ξ| ^ 2 * (‖∑ m ∈ Finset.range (K + 1), c m‖
            * ‖iteratedDeriv 2 (fun x : ℝ => Work.KMTContract.kmtEta x * ee (q * x)) ξ‖)
          = ‖∑ m ∈ Finset.range (K + 1), c m‖
            * (|ξ| ^ 2 * ‖iteratedDeriv 2 (fun x : ℝ =>
                Work.KMTContract.kmtEta x * ee (q * x)) ξ‖) := by ring
        _ ≤ 4 * (Q2 + 4 * Real.pi * |q| * Q1 + 4 * Real.pi ^ 2 * |q| ^ 2 * Q0) :=
            mul_le_mul hS4 (hF2 ξ) (by positivity) (by norm_num)
        _ ≤ C0 * 4 * 4 := by linarith [hQ2C, hC0nn]
  · have hs : (fun ξ : ℝ => ∑ m ∈ Finset.range (K + 1),
          c m * varphitildeNt P 0 (Nat.floor (a m)) k₂ t ξ) = 0 := by
      rw [hsymbol]
      funext ξ
      rw [if_neg hk, Pi.zero_apply]
      ring
    rw [hs]
    refine ⟨by positivity, ?_, ?_, ?_⟩
    · intro ξ
      rw [Pi.zero_apply, norm_zero]; positivity
    · intro ξ
      have hz1 : deriv (0 : ℝ → ℂ) ξ = 0 := by
        change deriv (fun _ : ℝ => (0 : ℂ)) ξ = 0
        exact deriv_const ξ 0
      rw [hz1, norm_zero, mul_zero]; positivity
    · intro ξ
      have hz2 : iteratedDeriv 2 (0 : ℝ → ℂ) ξ = 0 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
        change deriv (deriv (fun _ : ℝ => (0 : ℂ))) ξ = 0
        rw [show deriv (fun _ : ℝ => (0 : ℂ)) = fun _ => (0 : ℂ) from
          funext fun y => deriv_const y 0]
        exact deriv_const ξ 0
      rw [hz2, norm_zero, mul_zero]; positivity

end

end Work.KMTAreas.A7
