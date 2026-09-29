import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Chebyshev

namespace Commons.NumberTheory.Chebyshev

/-- If `c` divides (in the sense of `p`-adic exponent) the `p`-adic exponent of the lcm of a
finite set of nonzero natural numbers, then it is bounded by the exponent of one of them. -/
private lemma exists_factorization_ge_of_le_lcm_factorization {s : Finset ℕ}
    (hs : ∀ m ∈ s, m ≠ 0) {p c : ℕ} (hc : 0 < c)
    (h : c ≤ (s.lcm (fun m => m)).factorization p) :
    ∃ m ∈ s, c ≤ m.factorization p := by
  rw [Finset.factorization_lcm hs p] at h
  by_contra hcon
  have hcon' : ∀ m ∈ s, m.factorization p < c := by
    intro m hm
    by_contra hge
    exact hcon ⟨m, hm, not_lt.mp hge⟩
  have hle : s.sup (fun m => m.factorization p) ≤ c - 1 :=
    Finset.sup_le_iff.mpr (fun m hm => by have := hcon' m hm; omega)
  omega

theorem log_lcm_window_erase_zero_sub_theta_sub_bad_le (n k : ℕ) (hk : k ≤ n) :
    |Real.log ((((Finset.Icc (n - k) n).erase 0).lcm (fun m => m) : ℕ) : ℝ)
        - (Chebyshev.theta (n : ℝ)
            - ∑ p ∈ (Finset.Icc 1 n).filter
                (fun p => p.Prime ∧ ¬ (∃ m ∈ Finset.Icc (n - k) n, p ∣ m)), Real.log (p : ℝ))|
      ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  classical
  set W : Finset ℕ := (Finset.Icc (n - k) n).erase 0 with hWdef
  set L : ℕ := W.lcm (fun m => m) with hLdef
  set P : Finset ℕ := (Finset.Icc 1 n).filter
      (fun p => p.Prime ∧ ∃ m ∈ Finset.Icc (n - k) n, p ∣ m) with hPdef
  set B : Finset ℕ := (Finset.Icc 1 n).filter
      (fun p => p.Prime ∧ ¬ (∃ m ∈ Finset.Icc (n - k) n, p ∣ m)) with hBdef
  have hWsub : ∀ m ∈ W, m ∈ Finset.Icc (n - k) n := fun m hm => (Finset.mem_erase.mp (by
    rw [hWdef] at hm; exact hm)).2
  have hWne : ∀ m ∈ W, m ≠ 0 := fun m hm => (Finset.mem_erase.mp (by
    rw [hWdef] at hm; exact hm)).1
  have hLne : L ≠ 0 := by
    rw [hLdef, Finset.lcm_ne_zero_iff]
    exact hWne
  -- Every `p ∈ P` divides some element of the (zero-erased) window.
  have hmemW : ∀ p ∈ P, ∃ m ∈ W, p ∣ m := by
    intro p hpP
    rw [hPdef, Finset.mem_filter] at hpP
    obtain ⟨hpIcc, hpprime, m, hmIcc, hpm⟩ := hpP
    by_cases hm0 : m = 0
    · have hkn : k = n := by
        rw [Finset.mem_Icc] at hmIcc
        omega
      refine ⟨p, ?_, dvd_rfl⟩
      rw [hWdef, Finset.mem_erase]
      refine ⟨hpprime.ne_zero, ?_⟩
      rw [Finset.mem_Icc]
      rw [Finset.mem_Icc] at hpIcc
      omega
    · refine ⟨m, ?_, hpm⟩
      rw [hWdef, Finset.mem_erase]
      exact ⟨hm0, hmIcc⟩
  have hfac_pos : ∀ p ∈ P, 1 ≤ L.factorization p := by
    intro p hpP
    obtain ⟨m, hmW, hpm⟩ := hmemW p hpP
    have hpP' := hpP
    rw [hPdef, Finset.mem_filter] at hpP'
    obtain ⟨_, hpprime, _⟩ := hpP'
    have hdvd : p ∣ L := hpm.trans (Finset.dvd_lcm (f := fun m => m) hmW)
    exact (Nat.Prime.dvd_iff_one_le_factorization hpprime hLne).mp hdvd
  -- The support of the factorization of `L` lies in `P`.
  have hsuppP : L.factorization.support ⊆ P := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ L := (Nat.mem_primeFactors.mp hp).2.1
    obtain ⟨m, hmW, hpm⟩ :=
      exists_factorization_ge_of_le_lcm_factorization (s := W) hWne (p := p) (c := 1)
        (by norm_num)
        ((Nat.Prime.dvd_iff_one_le_factorization hpprime hLne).mp hdvd)
    have hmIcc : m ∈ Finset.Icc (n - k) n := hWsub m hmW
    have hpmdvd : p ∣ m :=
      (Nat.Prime.dvd_iff_one_le_factorization hpprime (hWne m hmW)).mpr hpm
    rw [hPdef, Finset.mem_filter]
    refine ⟨?_, hpprime, ⟨m, hmIcc, hpmdvd⟩⟩
    rw [Finset.mem_Icc]
    have hmle : m ≤ n := (Finset.mem_Icc.mp hmIcc).2
    have hple : p ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero (hWne m hmW)) hpmdvd
    exact ⟨hpprime.one_le, le_trans hple hmle⟩
  -- Step 1: `log L = ∑_{p ∈ P} v_p(L) log p`.
  have hlogL : Real.log (L : ℝ) = ∑ p ∈ P, ((L.factorization p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [Real.log_nat_eq_sum_factorization L]
    simp only [Finsupp.sum]
    refine Finset.sum_subset hsuppP (fun p _ hpns => ?_)
    rw [Finsupp.notMem_support_iff] at hpns
    simp [hpns]
  -- Step 2: `θ n = ∑_{p ∈ P} log p + ∑_{p ∈ B} log p`.
  have htheta_split : Chebyshev.theta (n : ℝ)
      = ∑ p ∈ P, Real.log (p : ℝ) + ∑ p ∈ B, Real.log (p : ℝ) := by
    rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
    have hQ0 : (Finset.Icc 0 n).filter (fun p => p.Prime)
        = (Finset.Icc 1 n).filter (fun p => p.Prime) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h0, hn⟩, hp⟩; exact ⟨⟨hp.one_le, hn⟩, hp⟩
      · rintro ⟨⟨h1, hn⟩, hp⟩; exact ⟨⟨by omega, hn⟩, hp⟩
    rw [hQ0]
    have hPeq : Finset.filter (fun p => ∃ m ∈ Finset.Icc (n - k) n, p ∣ m)
          (Finset.filter (fun p => p.Prime) (Finset.Icc 1 n)) = P := by
      rw [hPdef, Finset.filter_filter]
    have hBeq : Finset.filter (fun p => ¬ (∃ m ∈ Finset.Icc (n - k) n, p ∣ m))
          (Finset.filter (fun p => p.Prime) (Finset.Icc 1 n)) = B := by
      rw [hBdef, Finset.filter_filter]
    have key := Finset.sum_filter_add_sum_filter_not
      (Finset.filter (fun p => p.Prime) (Finset.Icc 1 n))
      (fun p => ∃ m ∈ Finset.Icc (n - k) n, p ∣ m) (fun p => Real.log (p : ℝ))
    rw [hPeq, hBeq] at key
    exact key.symm
  -- Step 3: identify the whole difference.
  have hmain : Real.log (L : ℝ)
        - (Chebyshev.theta (n : ℝ) - ∑ p ∈ B, Real.log (p : ℝ))
      = ∑ p ∈ P, ((L.factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [hlogL, htheta_split, add_sub_cancel_right, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hv : 1 ≤ L.factorization p := hfac_pos p hp
    rw [Nat.cast_sub hv]
    ring
  -- Nonnegativity of the identified difference.
  have hnonneg : 0 ≤ ∑ p ∈ P, ((L.factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ) := by
    refine Finset.sum_nonneg (fun p hp => ?_)
    have hpP := hp
    rw [hPdef, Finset.mem_filter] at hpP
    have hpprime : p.Prime := hpP.2.1
    have h1 : (0 : ℝ) ≤ ((L.factorization p - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ p from hpprime.one_le))
    exact mul_nonneg h1 h2
  -- Small-case: `log n ≥ 0`.
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact Real.log_nonneg (by exact_mod_cast hn)
  -- The set of primes with `v_p(L) ≥ 2`.
  set T : Finset ℕ := P.filter (fun p => 2 ≤ L.factorization p) with hTdef
  have hwit : ∀ p ∈ T, ∃ m ∈ W, p ^ (L.factorization p) ∣ m := by
    intro p hpT
    rw [hTdef, Finset.mem_filter] at hpT
    obtain ⟨hpP, hv2⟩ := hpT
    have hpP' := hpP
    rw [hPdef, Finset.mem_filter] at hpP'
    have hpprime : p.Prime := hpP'.2.1
    obtain ⟨m, hmW, hle⟩ :=
      exists_factorization_ge_of_le_lcm_factorization (s := W) hWne (p := p)
        (c := L.factorization p) (by omega) le_rfl
    exact ⟨m, hmW,
      (Nat.Prime.pow_dvd_iff_le_factorization hpprime (hWne m hmW)).mpr hle⟩
  have hsumT : ∑ p ∈ P, ((L.factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ)
      = ∑ p ∈ T, ((L.factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) (fun p hpP hpT => ?_)).symm
    have hv1 : 1 ≤ L.factorization p := hfac_pos p hpP
    have hv2 : ¬ (2 ≤ L.factorization p) := fun hh =>
      hpT (Finset.mem_filter.mpr ⟨hpP, hh⟩)
    have hzero : L.factorization p - 1 = 0 := by omega
    rw [hzero]; simp
  have hterm : ∀ p ∈ T, ((L.factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ)
      ≤ Real.log (n : ℝ) := by
    intro p hpT
    obtain ⟨m, hmW, hpm⟩ := hwit p hpT
    have hpT' := hpT
    rw [hTdef, Finset.mem_filter] at hpT'
    obtain ⟨hpP, hv2⟩ := hpT'
    have hpP' := hpP
    rw [hPdef, Finset.mem_filter] at hpP'
    have hpprime : p.Prime := hpP'.2.1
    have hmpos : 0 < m := Nat.pos_of_ne_zero (hWne m hmW)
    have hmle : m ≤ n := (Finset.mem_Icc.mp (hWsub m hmW)).2
    have hpv_le : p ^ L.factorization p ≤ n := le_trans (Nat.le_of_dvd hmpos hpm) hmle
    have hpow : p ^ (L.factorization p - 1) ≤ n :=
      le_trans (Nat.pow_le_pow_right hpprime.pos (Nat.sub_le _ _)) hpv_le
    have hlogeq : ((L.factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ)
        = Real.log ((p : ℝ) ^ (L.factorization p - 1)) := by
      rw [Real.log_pow]
    rw [hlogeq]
    refine Real.log_le_log ?_ ?_
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p from hpprime.pos)
      exact pow_pos hp0 _
    · rw [← Nat.cast_pow]
      exact_mod_cast hpow
  have hcard : (T.card : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hsub : T ⊆ Finset.Icc 2 (Nat.sqrt n) := by
      intro p hpT
      obtain ⟨m, hmW, hpm⟩ := hwit p hpT
      have hpT' := hpT
      rw [hTdef, Finset.mem_filter] at hpT'
      obtain ⟨hpP, hv2⟩ := hpT'
      have hpP' := hpP
      rw [hPdef, Finset.mem_filter] at hpP'
      have hpprime : p.Prime := hpP'.2.1
      have hmpos : 0 < m := Nat.pos_of_ne_zero (hWne m hmW)
      have hmle : m ≤ n := (Finset.mem_Icc.mp (hWsub m hmW)).2
      have hpv_le : p ^ L.factorization p ≤ n := le_trans (Nat.le_of_dvd hmpos hpm) hmle
      have hp2le : p ^ 2 ≤ p ^ L.factorization p :=
        Nat.pow_le_pow_right hpprime.pos hv2
      have hp2n : p ^ 2 ≤ n := le_trans hp2le hpv_le
      exact Finset.mem_Icc.mpr ⟨hpprime.two_le, Nat.le_sqrt'.mpr hp2n⟩
    have h1 : T.card ≤ (Finset.Icc 2 (Nat.sqrt n)).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    have h2 : T.card ≤ Nat.sqrt n := by omega
    calc (T.card : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast h2
      _ ≤ Real.sqrt (n : ℝ) := by
          rw [Real.le_sqrt (by positivity) (by positivity)]
          exact_mod_cast Nat.sqrt_le' n
  have hchain : ∑ p ∈ T, ((L.factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ)
      ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    calc ∑ p ∈ T, ((L.factorization p - 1 : ℕ) : ℝ) * Real.log (p : ℝ)
        ≤ ∑ _p ∈ T, Real.log (n : ℝ) := Finset.sum_le_sum hterm
      _ = (T.card : ℝ) * Real.log (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.sqrt (n : ℝ) * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_right hcard hlog_nn
      _ ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
          nlinarith [mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hlog_nn]
  have hnonneg' : 0 ≤ Real.log (L : ℝ)
      - (Chebyshev.theta (n : ℝ) - ∑ p ∈ B, Real.log (p : ℝ)) := by
    rw [hmain]; exact hnonneg
  rw [abs_of_nonneg hnonneg', hmain, hsumT]
  exact hchain

end Commons.NumberTheory.Chebyshev