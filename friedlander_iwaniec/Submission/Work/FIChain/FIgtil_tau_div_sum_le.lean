import Mathlib
import Submission.Work.FIChain.Defs

namespace Work.FIChain

open Finset

noncomputable section

/-- For squarefree `n ≠ 0`, the number of divisors is `∏_{p ∣ n} 2`. -/
lemma card_divisors_of_squarefree {n : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0) :
    n.divisors.card = ∏ p ∈ n.primeFactors, 2 := by
  rw [Nat.card_divisors hn0]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
  have hpn : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
  rw [Nat.factorization_eq_one_of_squarefree hn hp' hpn]

/-- The squarefree divisor sum `∑_{n ≤ Δ, Squarefree n} ∏_{p ∣ n} a p` is bounded by the Euler
product `∏_{p ≤ Δ, p prime} (1 + a p)`. -/
lemma sum_sqfree_prod_le_prod (Δ : ℕ) (a : ℕ → ℝ) (ha : ∀ p, 0 ≤ a p) :
    ∑ n ∈ (Finset.Icc 1 Δ).filter Squarefree, ∏ p ∈ n.primeFactors, a p
      ≤ ∏ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, (1 + a p) := by
  classical
  set S := (Finset.Icc 1 Δ).filter Nat.Prime with hS
  set T := (Finset.Icc 1 Δ).filter Squarefree with hT
  have hinj : Set.InjOn (fun n : ℕ => n.primeFactors) ↑T := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    rw [Finset.mem_filter] at hx hy
    have hxy' : x.primeFactors = y.primeFactors := hxy
    calc x = ∏ p ∈ x.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hx.2).symm
      _ = ∏ p ∈ y.primeFactors, p := by rw [hxy']
      _ = y := Nat.prod_primeFactors_of_squarefree hy.2
  have h1 : ∑ t ∈ T.image (fun n => n.primeFactors), ∏ p ∈ t, a p
      = ∑ n ∈ T, ∏ p ∈ n.primeFactors, a p := Finset.sum_image hinj
  rw [← h1]
  have hsub : T.image (fun n => n.primeFactors) ⊆ S.powerset := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨n, hnT, rfl⟩ := ht
    rw [Finset.mem_powerset]
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hnT
    rw [Nat.mem_primeFactors] at hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.1.pos, ?_⟩, hp.1⟩
    exact le_trans (Nat.le_of_dvd (by omega) hp.2.1) hnT.1.2
  have h2 : ∑ t ∈ T.image (fun n => n.primeFactors), ∏ p ∈ t, a p
      ≤ ∑ t ∈ S.powerset, ∏ p ∈ t, a p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun t _ _ => Finset.prod_nonneg fun p _ => ha p)
  have h3 : ∑ t ∈ S.powerset, ∏ p ∈ t, a p = ∏ p ∈ S, (1 + a p) := by
    have key := Finset.prod_add (s := S) (f := fun p => a p) (g := fun _ => (1:ℝ))
    simp only [Finset.prod_const_one, mul_one] at key
    rw [← key]
    exact Finset.prod_congr rfl (fun p _ => by ring)
  linarith [h2, h3.le]

/-- Term-level bound: for squarefree `ν ≠ 0` the `FIgtil`-weighted term is at most
`∏_{p ∣ ν} g(p)·2·(1 + 1/√p)`. -/
lemma FIgtil_mul_card_le (ν : ℕ) (hν : Squarefree ν) (hν0 : ν ≠ 0) :
    Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
        * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
      ≤ ∏ p ∈ ν.primeFactors,
          (Submission.ASP.FIg p * 2 * (1 + 1 / Real.sqrt (p : ℝ))) := by
  have hFI : Submission.ASP.FIgtil ν
      = ∏ p ∈ ν.primeFactors, Submission.ASP.gtilVal Submission.ASP.FIg p := by
    rw [Submission.ASP.FIgtil, if_pos hν]
  have hcard : (ν.divisors.card : ℝ) = ∏ p ∈ ν.primeFactors, (2:ℝ) := by
    rw [card_divisors_of_squarefree hν hν0]
    push_cast
    rfl
  rw [hFI, hcard, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
  · exact mul_nonneg (mul_nonneg
      (Submission.ASP.gtilVal_nonneg (Submission.ASP.FIg_nonneg _)
        (Submission.ASP.FI_gdens_prime_sq_le p (Nat.prime_of_mem_primeFactors hp)).1
        (Submission.ASP.FI_gdens_prime_nonneg (Nat.prime_of_mem_primeFactors hp)).2)
      (by norm_num)) (by positivity)
  · have hle : Submission.ASP.gtilVal Submission.ASP.FIg p ≤ Submission.ASP.FIg p := by
      have := Submission.ASP.FIgtil_correction_nonneg (Nat.prime_of_mem_primeFactors hp)
      linarith
    have step : Submission.ASP.gtilVal Submission.ASP.FIg p * 2 ≤ Submission.ASP.FIg p * 2 :=
      mul_le_mul_of_nonneg_right hle (by norm_num)
    exact mul_le_mul_of_nonneg_right step (by positivity)

theorem FIgtil_tau_div_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℕ, 3 ≤ Δ →
      (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
          Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
        ≤ C * (Real.log (Δ : ℝ)) ^ 3 := by
  obtain ⟨c, hc⟩ := Submission.ASP.FI_gdens_prime_sum
  obtain ⟨Cg, hCgpos, hCg⟩ := hc 10 (by norm_num)
  obtain ⟨C0, hC0pos, hC0⟩ := Submission.ASP.FI_gdens_bound
  refine ⟨Real.exp (64 * C0 + (5 / 2) * (c + Cg)), Real.exp_pos _, ?_⟩
  intro Δ hΔ
  set K : ℝ := 64 * C0 + (5 / 2) * (c + Cg) with hK
  -- logarithm facts
  have hl3 : (1:ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have hlogge : Real.log 3 ≤ Real.log (Δ:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hΔ)
  have hlog1 : (1:ℝ) < Real.log (Δ:ℝ) := lt_of_lt_of_le hl3 hlogge
  have hlogpos : 0 < Real.log (Δ:ℝ) := by linarith
  have hloglog : 0 ≤ Real.log (Real.log (Δ:ℝ)) := Real.log_nonneg hlog1.le
  -- the local weight
  set a : ℕ → ℝ := fun p => Submission.ASP.FIg p * 2 * (1 + 1/Real.sqrt (p:ℝ)) with ha
  have ha_nonneg : ∀ p, 0 ≤ a p := by
    intro p; rw [ha]
    exact mul_nonneg (mul_nonneg (Submission.ASP.FIg_nonneg p) (by norm_num)) (by positivity)
  -- step 1: reduce each term
  have hLHS : (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
      ≤ ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, ∏ p ∈ ν.primeFactors, a p := by
    refine Finset.sum_le_sum fun ν hν => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hν
    exact FIgtil_mul_card_le ν hν.2 (by omega)
  -- step 2: Euler-product bound
  have hcomb := sum_sqfree_prod_le_prod Δ a ha_nonneg
  -- step 3: the prime sum
  have hgsum : ∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, Submission.ASP.FIg p
      ≤ Real.log (Real.log (Δ:ℝ)) + c + Cg := by
    have h := hCg (Δ:ℝ) (by exact_mod_cast (by omega : 2 ≤ Δ))
    rw [Nat.floor_natCast] at h
    have hset : (Finset.Icc 2 Δ).filter Nat.Prime = (Finset.Icc 1 Δ).filter Nat.Prime := by
      ext p; simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨le_trans (by norm_num) h1, h2⟩, hp⟩
      · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨hp.two_le, h2⟩, hp⟩
    rw [hset] at h
    have h1 : ∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, Submission.ASP.FIg p
        - Real.log (Real.log (Δ:ℝ)) - c ≤ Cg / (Real.log (Δ:ℝ)) ^ (10:ℝ) := (abs_le.mp h).2
    have hpow : (1:ℝ) ≤ (Real.log (Δ:ℝ)) ^ (10:ℝ) := Real.one_le_rpow hlog1.le (by norm_num)
    have h2 : Cg / (Real.log (Δ:ℝ)) ^ (10:ℝ) ≤ Cg := div_le_self hCgpos.le hpow
    linarith
  -- step 4: split the weight sum at 16
  have hbnd : ∀ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => p < 16),
      a p ≤ 4 * C0 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpS, hp16⟩ := hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hpS
    obtain ⟨⟨hp1, hp2⟩, hpprime⟩ := hpS
    rw [ha]
    have hFIg : Submission.ASP.FIg p ≤ C0 / (p:ℝ) := hC0 p hpprime
    have hp1' : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp1
    have hdiv : C0 / (p:ℝ) ≤ C0 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hC0pos]
    have hb : (1 + 1/Real.sqrt (p:ℝ)) ≤ 2 := by
      have hsp : (1:ℝ) ≤ Real.sqrt (p:ℝ) := Real.one_le_sqrt.mpr hp1'
      have : 1 / Real.sqrt (p:ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]; exact hsp
      linarith
    calc Submission.ASP.FIg p * 2 * (1 + 1/Real.sqrt (p:ℝ))
        ≤ C0 * 2 * (1 + 1/Real.sqrt (p:ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_trans hFIg hdiv) (by norm_num)
      _ ≤ C0 * 2 * 2 := by
          refine mul_le_mul_of_nonneg_left hb ?_
          positivity
      _ = 4 * C0 := by ring
  have hsmall : ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => p < 16), a p
      ≤ 64 * C0 := by
    have hcard16 : (((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => p < 16)).card ≤ 16 := by
      calc _ ≤ (Finset.range 16).card := Finset.card_le_card (fun p hp => by
              rw [Finset.mem_filter] at hp; exact Finset.mem_range.mpr hp.2)
        _ = 16 := Finset.card_range 16
    calc ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => p < 16), a p
        ≤ _ • (4 * C0) :=
          Finset.sum_le_card_nsmul _ a (4 * C0) hbnd
      _ = (((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => p < 16)).card * (4 * C0) := by
          rw [nsmul_eq_mul]
      _ ≤ (16:ℝ) * (4 * C0) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard16) (by positivity)
      _ = 64 * C0 := by ring
  have hlarge : ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => ¬ p < 16), a p
      ≤ (5/2) * ∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, Submission.ASP.FIg p := by
    calc ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => ¬ p < 16), a p
        ≤ ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => ¬ p < 16),
            (5/2) * Submission.ASP.FIg p := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.mem_filter] at hp
          obtain ⟨hpS, hp16⟩ := hp
          rw [Finset.mem_filter, Finset.mem_Icc] at hpS
          rw [ha]
          have h16 : (16:ℝ) ≤ (p:ℝ) := by exact_mod_cast (by omega : 16 ≤ p)
          have hsp : (4:ℝ) ≤ Real.sqrt (p:ℝ) := by
            have := Real.sqrt_le_sqrt h16
            rwa [show Real.sqrt (16:ℝ) = 4 by
              rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
          have hle : (1:ℝ) + 1/Real.sqrt (p:ℝ) ≤ 5/4 := by
            have h1 : 1/Real.sqrt (p:ℝ) ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) hsp
            linarith
          calc Submission.ASP.FIg p * 2 * (1 + 1/Real.sqrt (p:ℝ))
              ≤ Submission.ASP.FIg p * 2 * (5/4) := by
                refine mul_le_mul_of_nonneg_left hle ?_
                exact mul_nonneg (Submission.ASP.FIg_nonneg p) (by norm_num)
            _ = (5/2) * Submission.ASP.FIg p := by ring
      _ = (5/2) * ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => ¬ p < 16),
            Submission.ASP.FIg p := (Finset.mul_sum _ _ _).symm
      _ ≤ (5/2) * ∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, Submission.ASP.FIg p := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun p _ _ => Submission.ASP.FIg_nonneg p)
  have hsum_a : ∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, a p
      ≤ 3 * Real.log (Real.log (Δ:ℝ)) + K := by
    have hsplit : ∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, a p
        = ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => p < 16), a p
          + ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => ¬ p < 16), a p :=
      (Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 Δ).filter Nat.Prime)
        (fun p => p < 16) a).symm
    have hlarge' : ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => ¬ p < 16), a p
        ≤ (5/2) * (Real.log (Real.log (Δ:ℝ)) + c + Cg) :=
      le_trans hlarge (mul_le_mul_of_nonneg_left hgsum (by norm_num))
    rw [hsplit]
    have hsum2 : ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => p < 16), a p
          + ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => ¬ p < 16), a p
        ≤ 64 * C0 + (5/2) * (Real.log (Real.log (Δ:ℝ)) + c + Cg) :=
      add_le_add hsmall hlarge'
    calc ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => p < 16), a p
          + ∑ p ∈ ((Finset.Icc 1 Δ).filter Nat.Prime).filter (fun p => ¬ p < 16), a p
        ≤ 64 * C0 + (5/2) * (Real.log (Real.log (Δ:ℝ)) + c + Cg) := hsum2
      _ = (5/2) * Real.log (Real.log (Δ:ℝ)) + K := by rw [hK]; ring
      _ ≤ 3 * Real.log (Real.log (Δ:ℝ)) + K := by linarith [hloglog]
  -- step 5: exponentiate
  have hprod1 : ∏ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, (1 + a p)
      ≤ Real.exp (∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, a p) := by
    have h : ∏ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, (1 + a p)
        ≤ ∏ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, Real.exp (a p) := by
      refine Finset.prod_le_prod₀ (fun p hp => by linarith [ha_nonneg p]) (fun p hp => ?_)
      have := Real.add_one_le_exp (a p); linarith
    calc ∏ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, (1 + a p)
        ≤ ∏ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, Real.exp (a p) := h
      _ = Real.exp (∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, a p) :=
          (Real.exp_sum _ _).symm
  have hexpK : Real.exp (3 * Real.log (Real.log (Δ:ℝ)) + K)
      = Real.exp K * (Real.log (Δ:ℝ))^3 := by
    rw [Real.exp_add]
    have he : Real.exp (3 * Real.log (Real.log (Δ:ℝ))) = (Real.log (Δ:ℝ))^3 := by
      rw [show (3:ℝ) * Real.log (Real.log (Δ:ℝ))
          = ((3:ℕ):ℝ) * Real.log (Real.log (Δ:ℝ)) by norm_num]
      rw [Real.exp_nat_mul, Real.exp_log hlogpos]
    rw [he]; ring
  calc (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
      ≤ ∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, ∏ p ∈ ν.primeFactors, a p := hLHS
    _ ≤ ∏ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, (1 + a p) := hcomb
    _ ≤ Real.exp (∑ p ∈ (Finset.Icc 1 Δ).filter Nat.Prime, a p) := hprod1
    _ ≤ Real.exp (3 * Real.log (Real.log (Δ:ℝ)) + K) := Real.exp_le_exp.mpr hsum_a
    _ = Real.exp K * (Real.log (Δ:ℝ))^3 := hexpK

end

end Work.FIChain
