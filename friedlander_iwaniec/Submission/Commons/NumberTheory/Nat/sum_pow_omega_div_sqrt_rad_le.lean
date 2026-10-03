import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Submission.Commons.NumberTheory.Nat.sum_recip_sqrt_mul_radical_le

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Commons.NumberTheory.Nat

namespace SumPowOmega

/-- Local factor for the weighted sum: `wa a p 0 = 1` and `wa a p k = a * w p k` for `k ≥ 1`. -/
noncomputable def wa (a : ℝ) (p k : ℕ) : ℝ :=
  if k = 0 then 1 else a * SumRad.w p k

lemma wa_zero (a : ℝ) (p : ℕ) : wa a p 0 = 1 := by simp [wa]

lemma wa_succ (a : ℝ) (p k : ℕ) : wa a p (k+1) = a * SumRad.w p (k+1) := by
  simp [wa]

lemma wa_nonneg {a : ℝ} (ha : 0 ≤ a) {p k : ℕ} (hp : p.Prime) : 0 ≤ wa a p k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [wa]
  · simp only [wa, if_neg hk]
    exact mul_nonneg ha (SumRad.w_nonneg hp)

/-- The product of the local factors along `n.primeFactors` recovers the summand. -/
lemma prod_wa_eq (a : ℝ) (n : ℕ) (hn : n ≠ 0) {S : Finset ℕ}
    (hsub : n.primeFactors ⊆ S) (hprime : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, wa a p (n.factorization p)
      = a ^ n.primeFactors.card / (Real.sqrt (n : ℝ) * (SumRad.rad n : ℝ)) := by
  have hzero : ∀ p ∈ S, p ∉ n.primeFactors → wa a p (n.factorization p) = 1 := by
    intro p _ hpn
    have hfac : n.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact hpn
    simp [wa, hfac]
  rw [← Finset.prod_subset hsub hzero]
  have hcongr : ∏ p ∈ n.primeFactors, wa a p (n.factorization p)
      = ∏ p ∈ n.primeFactors, (a * SumRad.w p (n.factorization p)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hne : n.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hp
    simp only [wa, if_neg hne]
  rw [hcongr, Finset.prod_mul_distrib, Finset.prod_const]
  have hw := SumRad.prod_w_eq n hn (Finset.Subset.refl _)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [hw, mul_one_div]

/-- The weighted sum is bounded by the Euler product of the local factors. -/
theorem sum_le_prod_wa (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        a ^ n.primeFactors.card / (Real.sqrt (n : ℝ) * (SumRad.rad n : ℝ)))
      ≤ ∏ p ∈ (Finset.range (N+1)).filter Nat.Prime,
          (∑ k ∈ Finset.range (N+1), wa a p k) := by
  classical
  set S : Finset ℕ := (Finset.range (N+1)).filter Nat.Prime with hS
  have hprimeS : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hmemS : ∀ p, p.Prime → p ≤ N → p ∈ S := by
    intro p hp hpN
    rw [hS]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpN), hp⟩
  have hL : (∑ n ∈ Finset.Icc 1 N,
        a ^ n.primeFactors.card / (Real.sqrt (n : ℝ) * (SumRad.rad n : ℝ)))
      = ∑ n ∈ Finset.Icc 1 N, ∏ i : ↥S, wa a (i:ℕ) (n.factorization (i:ℕ)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have hsub : n.primeFactors ⊆ S := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hdvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
      have hle : p ≤ N := le_trans (Nat.le_of_dvd (by omega) hdvd) (Finset.mem_Icc.mp hn).2
      exact hmemS p hpp hle
    rw [← prod_wa_eq a n hn0 hsub hprimeS, ← Finset.prod_attach S (fun p => wa a p (n.factorization p)),
      ← Finset.univ_eq_attach S]
  rw [hL]
  set Φ : ℕ → (↥S → ℕ) := fun n i => n.factorization (i : ℕ) with hΦ
  have hinj : Set.InjOn Φ ↑(Finset.Icc 1 N) := by
    intro a' ha' b hb hab
    rw [Finset.mem_coe] at ha' hb
    have ha1 : 1 ≤ a' := (Finset.mem_Icc.mp ha').1
    have haN : a' ≤ N := (Finset.mem_Icc.mp ha').2
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hbN : b ≤ N := (Finset.mem_Icc.mp hb).2
    refine Nat.eq_of_factorization_eq (by omega) (by omega) fun p => ?_
    by_cases hp : p.Prime
    · by_cases hpN : p ≤ N
      · have hpS : p ∈ S := hmemS p hp hpN
        exact congrFun hab ⟨p, hpS⟩
      · have ha0 : a'.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
          (fun h => hpN (le_trans (Nat.le_of_dvd (by omega) h) haN))
        have hb0 : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
          (fun h => hpN (le_trans (Nat.le_of_dvd (by omega) h) hbN))
        rw [ha0, hb0]
    · rw [Nat.factorization_eq_zero_of_not_prime a' hp,
        Nat.factorization_eq_zero_of_not_prime b hp]
  have hmem_img : ∀ y ∈ (Finset.Icc 1 N).image Φ,
      y ∈ Fintype.piFinset (fun _ : ↥S => Finset.range (N+1)) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (SumRad.factorization_le_of_mem hn (hprimeS i.1 i.2))
  have hprod : ∏ p ∈ S, (∑ k ∈ Finset.range (N+1), wa a p k)
      = ∑ x ∈ Fintype.piFinset (fun _ : ↥S => Finset.range (N+1)),
          ∏ i : ↥S, wa a (i:ℕ) (x i) := by
    rw [← Finset.prod_attach S (fun p => ∑ k ∈ Finset.range (N+1), wa a p k)]
    rw [← Finset.univ_eq_attach S]
    exact Finset.prod_univ_sum (fun _ : ↥S => Finset.range (N+1))
      (fun (i : ↥S) (k : ℕ) => wa a (i:ℕ) k)
  have himg := Finset.sum_image (f := fun y : (↥S → ℕ) => ∏ i : ↥S, wa a (↑i) (y i)) hinj
  rw [hprod]
  rw [show (∑ n ∈ Finset.Icc 1 N, ∏ i : ↥S, wa a (↑i) (n.factorization ↑i))
        = ∑ n ∈ Finset.Icc 1 N, ∏ i : ↥S, wa a (↑i) (Φ n i) from by
      refine Finset.sum_congr rfl fun n _ => Finset.prod_congr rfl fun i _ => ?_
      rw [hΦ]]
  rw [← himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg hmem_img (fun y _ _ => ?_)
  exact Finset.prod_nonneg fun i _ => wa_nonneg ha (hprimeS i.1 i.2)

/-- Bound on the local factor: `∑_{k ≤ N} wa a p k ≤ 1 + a·cg p`. -/
lemma sum_wa_le (a : ℝ) (ha : 0 ≤ a) (p N : ℕ) (hp : p.Prime) :
    (∑ k ∈ Finset.range (N+1), wa a p k) ≤ 1 + a * SumRad.cg p := by
  have hwN : (∑ i ∈ Finset.range N, SumRad.w p (i+1)) ≤ SumRad.cg p := by
    have h := SumRad.sum_w_le p N hp
    rw [Finset.sum_range_succ', SumRad.w_zero] at h
    linarith
  rw [Finset.sum_range_succ', wa_zero]
  rw [Finset.sum_congr rfl (fun i _ => wa_succ a p i), ← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left hwN ha
  linarith

/-- Uniform bound `∏_{p ≤ N prime} (1 + cg p) ≤ 6`. -/
lemma prod_one_add_cg_le (N : ℕ) :
    (∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 + SumRad.cg p)) ≤ 6 := by
  set S := (Finset.range (N+1)).filter Nat.Prime with hS
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun p => p ≤ 7) (fun p => 1 + SumRad.cg p)]
  have hset : S.filter (fun p => ¬ p ≤ 7) = S.filter (fun p => 7 < p) :=
    Finset.filter_congr fun p _ => by omega
  rw [hset]
  have hsub : S.filter (fun p => p ≤ 7) ⊆ ({2,3,5,7} : Finset ℕ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpS, hp7⟩ := hp
    have hpp : p.Prime := (Finset.mem_filter.mp hpS).2
    have hp2 : 2 ≤ p := hpp.two_le
    have hp8 : p < 8 := by omega
    interval_cases p
    · simp
    · simp
    · exfalso; norm_num at hpp
    · simp
    · exfalso; norm_num at hpp
    · simp
  have hsmall : (∏ p ∈ S.filter (fun p => p ≤ 7), (1 + SumRad.cg p)) ≤ 4.057 :=
    le_trans (Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun p _ => by linarith [SumRad.cg_nonneg p])
      (fun p _ _ => by linarith [SumRad.cg_nonneg p])) SumRad.prod_small_primes_le
  have htail : (∏ p ∈ S.filter (fun p => 7 < p), (1 + SumRad.cg p))
      ≤ (1 + 0.276) * (1/(1 - 1.432/18)) := by
    have hstep : (∏ p ∈ S.filter (fun p => 7 < p), (1 + SumRad.cg p))
        ≤ (∏ p ∈ S.filter (fun p => 7 < p), (1 + SumRad.sqp p))
          * (∏ p ∈ S.filter (fun p => 7 < p), (1 + SumRad.dpr p)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun p _ => by linarith [SumRad.cg_nonneg p]) (fun p hp => ?_)
      have hpp : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      exact SumRad.cg_le p hpp (Finset.mem_filter.mp hp).2
    have hsq := SumRad.prod_sqp_le N
    have hdp := SumRad.prod_dpr_le N
    have e1 : (0:ℝ) ≤ ∏ p ∈ S.filter (fun p => 7 < p), (1 + SumRad.sqp p) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hp' : (0:ℝ) < p := by
        have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        exact_mod_cast this.pos
      have : (0:ℝ) < Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr hp'
      have : (0:ℝ) < (p:ℝ) * Real.sqrt (p:ℝ) := mul_pos hp' this
      simp only [SumRad.sqp]
      positivity
    nlinarith [hstep, hsq, hdp, e1]
  have e : 0 ≤ ∏ p ∈ S.filter (fun p => 7 < p), (1 + SumRad.cg p) :=
    Finset.prod_nonneg fun p _ => by linarith [SumRad.cg_nonneg p]
  have hmul := mul_le_mul hsmall htail e (by norm_num : (0:ℝ) ≤ 4.057)
  nlinarith [hmul]

end SumPowOmega

open SumPowOmega

theorem sum_pow_omega_div_sqrt_rad_le (a : ℝ) (ha : 0 ≤ a) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N,
        a ^ n.primeFactors.card /
          (Real.sqrt (n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ))) ≤ K := by
  refine ⟨6 ^ (max a 1), Real.rpow_pos_of_pos (by norm_num) _, fun N => ?_⟩
  set S : Finset ℕ := (Finset.range (N+1)).filter Nat.Prime with hS
  have hprimeS : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have h1 := SumPowOmega.sum_le_prod_wa a ha N
  simp only [SumRad.rad] at h1
  rw [← hS] at h1
  have h2 : ∏ p ∈ S, (∑ k ∈ Finset.range (N+1), SumPowOmega.wa a p k)
      ≤ ∏ p ∈ S, (1 + SumRad.cg p) ^ (max a 1) := by
    refine Finset.prod_le_prod₀
      (fun p hp => Finset.sum_nonneg (fun k _ => SumPowOmega.wa_nonneg (k := k) ha (hprimeS p hp)))
      (fun p hp => ?_)
    have hloc := SumPowOmega.sum_wa_le a ha p N (hprimeS p hp)
    have hb := one_add_mul_self_le_rpow_one_add (s := SumRad.cg p)
      (by linarith [SumRad.cg_nonneg p]) (le_max_right a 1)
    have hacg : a * SumRad.cg p ≤ (max a 1) * SumRad.cg p :=
      mul_le_mul_of_nonneg_right (le_max_left a 1) (SumRad.cg_nonneg p)
    linarith
  have h3 : ∏ p ∈ S, (1 + SumRad.cg p) ^ (max a 1)
      = (∏ p ∈ S, (1 + SumRad.cg p)) ^ (max a 1) :=
    Real.finsetProd_rpow S (fun p => 1 + SumRad.cg p)
      (fun p _ => by linarith [SumRad.cg_nonneg p]) (max a 1)
  have h4 : (∏ p ∈ S, (1 + SumRad.cg p)) ^ (max a 1) ≤ 6 ^ (max a 1) := by
    refine Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ => by linarith [SumRad.cg_nonneg p]))
      ?_ (le_trans zero_le_one (le_max_right a 1))
    have hp := SumPowOmega.prod_one_add_cg_le N
    simpa only [hS] using hp
  calc (∑ n ∈ Finset.Icc 1 N,
          a ^ n.primeFactors.card / (Real.sqrt (n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ)))
      ≤ ∏ p ∈ S, (∑ k ∈ Finset.range (N+1), SumPowOmega.wa a p k) := h1
    _ ≤ ∏ p ∈ S, (1 + SumRad.cg p) ^ (max a 1) := h2
    _ = (∏ p ∈ S, (1 + SumRad.cg p)) ^ (max a 1) := h3
    _ ≤ 6 ^ (max a 1) := h4

end Commons.NumberTheory.Nat