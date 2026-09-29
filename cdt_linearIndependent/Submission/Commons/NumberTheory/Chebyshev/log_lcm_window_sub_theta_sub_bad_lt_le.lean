import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.NumberTheory.Chebyshev

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Chebyshev

/-- `θ` at a natural number, written as a sum over the primes `≤ n`. -/
lemma theta_nat_eq_sum_primes_window (n : ℕ) :
    Chebyshev.theta (n : ℝ) = ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log (p : ℝ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, hpn⟩, hp⟩; exact ⟨⟨hp.one_le, hpn⟩, hp⟩
  · rintro ⟨⟨h1, hpn⟩, hp⟩; exact ⟨⟨Nat.zero_le _, hpn⟩, hp⟩

/-- `log n` expanded over the prime factorization of `n ≠ 0`. -/
lemma log_nat_eq_sum_factorization_window {n : ℕ} (hn : n ≠ 0) :
    Real.log (n : ℝ) = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  have hcast : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p : ℕ) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl (fun p _ => by rw [Nat.cast_pow])
  rw [hcast, Real.log_prod]
  · exact Finset.sum_congr rfl (fun p _ => by rw [Real.log_pow])
  · intro p hp
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero)

/-- If a prime power divides the lcm of a nonempty family of nonzero naturals, it divides
one of the members. -/
lemma prime_pow_dvd_finset_lcm_window {p k : ℕ} (hp : p.Prime) {s : Finset ℕ} (hs : s.Nonempty)
    (hf : ∀ a ∈ s, a ≠ 0) (h : p ^ k ∣ s.lcm (fun m => m)) : ∃ a ∈ s, p ^ k ∣ a := by
  have hne : s.lcm (fun m => m) ≠ 0 := Finset.lcm_ne_zero_iff.mpr hf
  have hk : k ≤ (s.lcm (fun m => m)).factorization p :=
    (hp.pow_dvd_iff_le_factorization hne).mp h
  obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup s hs (fun m => m.factorization p)
  refine ⟨a, ha, (hp.pow_dvd_iff_le_factorization (hf a ha)).mpr ?_⟩
  rw [← hsup, ← Finset.factorization_lcm hf p]
  exact hk

theorem log_lcm_window_sub_theta_sub_bad_lt_le (n k : ℕ) (hk : k < n) :
    |Real.log (((Finset.Icc (n - k) n).lcm (fun m => m) : ℕ) : ℝ)
        - (Chebyshev.theta (n : ℝ)
            - ∑ p ∈ (Finset.Icc 1 n).filter
                (fun p => p.Prime ∧ ¬ (∃ m ∈ Finset.Icc (n - k) n, p ∣ m)), Real.log (p : ℝ))|
      ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  classical
  have hn1 : 1 ≤ n := by omega
  set W : Finset ℕ := Finset.Icc (n - k) n with hWdef
  set L : ℕ := W.lcm (fun m => m) with hLdef
  set Bsum : ℝ :=
    ∑ p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ ¬ (∃ m ∈ W, p ∣ m)),
      Real.log (p : ℝ) with hBdef
  set G : Finset ℕ :=
    (Finset.Icc 1 n).filter (fun p => p.Prime ∧ ∃ m ∈ W, p ∣ m) with hGdef
  have hWspec : ∀ m, m ∈ W ↔ n - k ≤ m ∧ m ≤ n := by
    intro m; rw [hWdef, Finset.mem_Icc]
  have hWmem : ∀ m ∈ W, 1 ≤ m := by
    intro m hm; have := (hWspec m).mp hm; omega
  have hWne : ∀ m ∈ W, m ≠ 0 := by
    intro m hm; have := hWmem m hm; omega
  have hWnonempty : W.Nonempty := ⟨n, (hWspec n).mpr ⟨by omega, le_rfl⟩⟩
  have hLnz : L ≠ 0 := by rw [hLdef]; exact Finset.lcm_ne_zero_iff.mpr hWne
  -- The primes dividing the lcm are exactly the "good" primes.
  have hpf : L.primeFactors = G := by
    ext p
    rw [Nat.mem_primeFactors, hGdef, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hp, hdvd, -⟩
      rw [hLdef] at hdvd
      obtain ⟨m, hmW, hpm⟩ :=
        prime_pow_dvd_finset_lcm_window hp hWnonempty hWne (k := 1) (by simpa using hdvd)
      rw [pow_one] at hpm
      have hmn : m ≤ n := ((hWspec m).mp hmW).2
      refine ⟨⟨hp.one_le, le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (hWne m hmW)) hpm) hmn⟩,
        hp, m, hmW, hpm⟩
    · rintro ⟨⟨h1, hpn⟩, hp, m, hmW, hpm⟩
      exact ⟨hp, by rw [hLdef]; exact dvd_trans hpm (Finset.dvd_lcm hmW), hLnz⟩
  have hlogL : Real.log (L : ℝ) = ∑ p ∈ G, (L.factorization p : ℝ) * Real.log (p : ℝ) := by
    rw [log_nat_eq_sum_factorization_window hLnz, hpf]
  -- `θ n` splits into the sum over good and over bad primes.
  have htheta : Chebyshev.theta (n : ℝ)
      = ∑ p ∈ Finset.Icc 1 n, (if p.Prime then Real.log (p : ℝ) else 0) := by
    rw [theta_nat_eq_sum_primes_window n, Finset.sum_filter]
  have hBsum_eq : Bsum
      = ∑ p ∈ Finset.Icc 1 n,
          (if p.Prime ∧ ¬ (∃ m ∈ W, p ∣ m) then Real.log (p : ℝ) else 0) := by
    rw [hBdef, Finset.sum_filter]
  have hGsum_eq : (∑ p ∈ G, Real.log (p : ℝ))
      = ∑ p ∈ Finset.Icc 1 n,
          (if p.Prime ∧ ∃ m ∈ W, p ∣ m then Real.log (p : ℝ) else 0) := by
    rw [hGdef, Finset.sum_filter]
  have htheta_split : Chebyshev.theta (n : ℝ) = Bsum + ∑ p ∈ G, Real.log (p : ℝ) := by
    rw [htheta, hBsum_eq, hGsum_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hpp : p.Prime
    · by_cases hg : ∃ m ∈ W, p ∣ m
      · simp [hpp, hg]
      · simp [hpp, hg]
    · simp [hpp]
  have htheta' : Chebyshev.theta (n : ℝ) - Bsum = ∑ p ∈ G, Real.log (p : ℝ) := by
    rw [htheta_split]; ring
  -- The signed quantity is a sum of nonnegative terms.
  have hmain : Real.log (L : ℝ) - (Chebyshev.theta (n : ℝ) - Bsum)
      = ∑ p ∈ G, ((L.factorization p : ℝ) - 1) * Real.log (p : ℝ) := by
    rw [htheta', hlogL, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  have hnonneg : 0 ≤ Real.log (L : ℝ) - (Chebyshev.theta (n : ℝ) - Bsum) := by
    rw [hmain]
    refine Finset.sum_nonneg (fun p hp => ?_)
    have hp' : p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ ∃ m ∈ W, p ∣ m) := hGdef ▸ hp
    obtain ⟨hmem, hpp, m, hmW, hpm⟩ := Finset.mem_filter.mp hp'
    have hp1 : 1 ≤ p := (Finset.mem_Icc.mp hmem).1
    have hdvdL : p ∣ L := by rw [hLdef]; exact dvd_trans hpm (Finset.dvd_lcm hmW)
    have hv1 : 1 ≤ L.factorization p :=
      (hpp.pow_dvd_iff_le_factorization (k := 1) hLnz).mp (by simpa using hdvdL)
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
    have hvr : (1 : ℝ) ≤ (L.factorization p : ℝ) := by exact_mod_cast hv1
    exact mul_nonneg (by linarith) hlogp
  rw [abs_of_nonneg hnonneg, hmain]
  -- Bound the sum: only primes `p` with `p ^ 2 ≤ n` contribute.
  set S : Finset ℕ := G.filter (fun p => 2 ≤ L.factorization p) with hSdef
  have hSsplit : ∑ p ∈ G, ((L.factorization p : ℝ) - 1) * Real.log (p : ℝ)
      = ∑ p ∈ S, ((L.factorization p : ℝ) - 1) * Real.log (p : ℝ) := by
    have hzero : ∑ p ∈ G.filter (fun p => ¬ 2 ≤ L.factorization p),
          ((L.factorization p : ℝ) - 1) * Real.log (p : ℝ) = 0 := by
      refine Finset.sum_eq_zero (fun p hp => ?_)
      rw [Finset.mem_filter] at hp
      obtain ⟨hpG, hpv⟩ := hp
      have hp' : p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ ∃ m ∈ W, p ∣ m) :=
        hGdef ▸ hpG
      obtain ⟨hmem, hpp, m, hmW, hpm⟩ := Finset.mem_filter.mp hp'
      have hdvdL : p ∣ L := by rw [hLdef]; exact dvd_trans hpm (Finset.dvd_lcm hmW)
      have hv1 : 1 ≤ L.factorization p :=
        (hpp.pow_dvd_iff_le_factorization (k := 1) hLnz).mp (by simpa using hdvdL)
      have hv : L.factorization p = 1 := by omega
      simp [hv]
    rw [← Finset.sum_filter_add_sum_filter_not G (fun p => 2 ≤ L.factorization p)
      (fun p => ((L.factorization p : ℝ) - 1) * Real.log (p : ℝ)), hzero, add_zero, hSdef]
  rw [hSsplit]
  have hterm : ∀ p ∈ S, ((L.factorization p : ℝ) - 1) * Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
    intro p hp
    have hp' : p ∈ G.filter (fun p => 2 ≤ L.factorization p) := hSdef ▸ hp
    rw [Finset.mem_filter] at hp'
    obtain ⟨hpG, hpv⟩ := hp'
    have hp'' : p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ ∃ m ∈ W, p ∣ m) :=
      hGdef ▸ hpG
    obtain ⟨hmem, hpp, m, hmW, hpm⟩ := Finset.mem_filter.mp hp''
    have hdvd : p ^ (L.factorization p) ∣ L :=
      (hpp.pow_dvd_iff_le_factorization hLnz).mpr le_rfl
    obtain ⟨m', hmW', hpm'⟩ := prime_pow_dvd_finset_lcm_window hpp hWnonempty hWne hdvd
    have hm'le : m' ≤ n := ((hWspec m').mp hmW').2
    have hle : p ^ L.factorization p ≤ n :=
      le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (hWne m' hmW')) hpm') hm'le
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    have hvr : (1 : ℝ) ≤ (L.factorization p : ℝ) := by
      have : 1 ≤ L.factorization p := by omega
      exact_mod_cast this
    calc ((L.factorization p : ℝ) - 1) * Real.log (p : ℝ)
        ≤ (L.factorization p : ℝ) * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hlogp
      _ = Real.log ((p : ℝ) ^ (L.factorization p)) :=
            (Real.log_pow (p : ℝ) (L.factorization p)).symm
      _ = Real.log (((p ^ L.factorization p : ℕ) : ℝ)) := by rw [Nat.cast_pow]
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (by
            have : 0 < p ^ L.factorization p := pow_pos hpp.pos _
            exact_mod_cast this) (by exact_mod_cast hle)
  have hcard : (S.card : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hSsub : S ⊆ Finset.Icc 1 ⌊Real.sqrt (n : ℝ)⌋₊ := by
      intro p hp
      have hp' : p ∈ G.filter (fun p => 2 ≤ L.factorization p) := hSdef ▸ hp
      rw [Finset.mem_filter] at hp'
      obtain ⟨hpG, hpv⟩ := hp'
      have hp'' : p ∈ (Finset.Icc 1 n).filter (fun p => p.Prime ∧ ∃ m ∈ W, p ∣ m) :=
        hGdef ▸ hpG
      obtain ⟨hmem, hpp, m, hmW, hpm⟩ := Finset.mem_filter.mp hp''
      have hp1 : 1 ≤ p := (Finset.mem_Icc.mp hmem).1
      have hdvd : p ^ 2 ∣ L := (hpp.pow_dvd_iff_le_factorization hLnz).mpr (by omega)
      obtain ⟨m', hmW', hpm'⟩ := prime_pow_dvd_finset_lcm_window hpp hWnonempty hWne hdvd
      have hle : p ^ 2 ≤ n :=
        le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero (hWne m' hmW')) hpm') ((hWspec m').mp hmW').2
      have hsq : ((p : ℝ)) ^ 2 ≤ (n : ℝ) := by
        have h2 : ((p ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
        rwa [Nat.cast_pow] at h2
      have hpsqrt : (p : ℝ) ≤ Real.sqrt (n : ℝ) :=
        (Real.le_sqrt (by positivity) (by positivity)).mpr hsq
      rw [Finset.mem_Icc]
      exact ⟨hp1, Nat.le_floor hpsqrt⟩
    have h1 : ((Finset.Icc 1 ⌊Real.sqrt (n : ℝ)⌋₊).card : ℝ) = (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
      simp
    calc (S.card : ℝ) ≤ ((Finset.Icc 1 ⌊Real.sqrt (n : ℝ)⌋₊).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hSsub
      _ = (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := h1
      _ ≤ Real.sqrt (n : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  calc ∑ p ∈ S, ((L.factorization p : ℝ) - 1) * Real.log (p : ℝ)
      ≤ ∑ p ∈ S, Real.log (n : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * Real.log (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.sqrt (n : ℝ) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hcard hlogn
    _ ≤ 2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
        nlinarith [Real.sqrt_nonneg (n : ℝ), hlogn]

end Commons.NumberTheory.Chebyshev