import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_bound_of_squarefree
import Submission.Commons.NumberTheory.Sieve.sum_primes_recip_le_loglog

namespace Commons.NumberTheory.Sieve

open Finset

/-- Termwise rewriting of the weighted summand on squarefree `d`: distributing the
fixed factor `2 ^ (20/3)` over the prime factors. -/
private lemma term_eq_prod_rpow (g : ℕ → ℝ) {d : ℕ} (hd : 1 ≤ d) (hsq : Squarefree d) :
    ((Nat.divisors d).card : ℝ) ^ (20 / 3 : ℝ) * ∏ p ∈ d.primeFactors, g p
      = ∏ p ∈ d.primeFactors, ((2 : ℝ) ^ (20 / 3 : ℝ) * g p) := by
  have hd0 : d ≠ 0 := by omega
  have hcard : (Nat.divisors d).card = 2 ^ (d.primeFactors).card :=
    Commons.NumberTheory.FriedlanderIwaniec.card_divisors_of_squarefree hd0 hsq
  have hcast : ((2 ^ (d.primeFactors).card : ℕ) : ℝ) = (2 : ℝ) ^ (d.primeFactors).card :=
    Nat.cast_pow 2 _
  have hpow : ((2 : ℝ) ^ (d.primeFactors).card) ^ (20 / 3 : ℝ)
      = ((2 : ℝ) ^ (20 / 3 : ℝ)) ^ (d.primeFactors).card := by
    have h1 : ((2 : ℝ) ^ (d.primeFactors).card) = (2 : ℝ) ^ (((d.primeFactors).card : ℕ) : ℝ) :=
      (Real.rpow_natCast (2 : ℝ) ((d.primeFactors).card)).symm
    calc ((2 : ℝ) ^ (d.primeFactors).card) ^ (20 / 3 : ℝ)
        = ((2 : ℝ) ^ (((d.primeFactors).card : ℕ) : ℝ)) ^ (20 / 3 : ℝ) := by rw [h1]
      _ = (2 : ℝ) ^ ((((d.primeFactors).card : ℕ) : ℝ) * (20 / 3 : ℝ)) :=
            (Real.rpow_mul (by norm_num) _ _).symm
      _ = (2 : ℝ) ^ ((20 / 3 : ℝ) * (((d.primeFactors).card : ℕ) : ℝ)) := by ring_nf
      _ = ((2 : ℝ) ^ (20 / 3 : ℝ)) ^ (((d.primeFactors).card : ℕ) : ℝ) :=
            Real.rpow_mul (by norm_num) _ _
      _ = ((2 : ℝ) ^ (20 / 3 : ℝ)) ^ (d.primeFactors).card := Real.rpow_natCast _ _
  rw [hcard, hcast, hpow, Finset.prod_mul_distrib, Finset.prod_const]

/-- Euler-product (squarefree) bound: the sum over squarefree `d ≤ y` of a
product over the prime factors is bounded by the full Euler product over the
primes below `y + 1`. -/
private lemma sum_sqfree_primeFactors_le_prod_euler (f : ℕ → ℝ)
    (hf : ∀ p, p.Prime → 0 ≤ f p) (y : ℕ) :
    (∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d),
        ∏ p ∈ d.primeFactors, f p)
      ≤ ∏ p ∈ Nat.primesBelow (y + 1), (1 + f p) := by
  classical
  set F : Finset ℕ := (Finset.Icc 1 y).filter (fun d => Squarefree d) with hF
  set P : Finset ℕ := Nat.primesBelow (y + 1) with hP
  have hmem1 : ∀ d ∈ F, 1 ≤ d := by
    intro d hd
    rw [hF] at hd
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  have hmemle : ∀ d ∈ F, d ≤ y := by
    intro d hd
    rw [hF] at hd
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
  have hmemsq : ∀ d ∈ F, Squarefree d := by
    intro d hd
    rw [hF] at hd
    exact (Finset.mem_filter.mp hd).2
  have hinj : Set.InjOn (fun d : ℕ => d.primeFactors) F := by
    intro m hm n hn hmn
    have hmf := hmemsq m hm
    have hnf := hmemsq n hn
    have hmn' : m.primeFactors = n.primeFactors := hmn
    rw [← Nat.prod_primeFactors_of_squarefree hmf, hmn',
        Nat.prod_primeFactors_of_squarefree hnf]
  have hsub : F.image (fun d : ℕ => d.primeFactors) ⊆ P.powerset := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨d, hd, rfl⟩ := ht
    rw [Finset.mem_powerset]
    intro p hp
    rw [hP, Nat.mem_primesBelow]
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hprime, hdvd, _⟩ := hp
    refine ⟨?_, hprime⟩
    have hdle := hmemle d hd
    have hdge := hmem1 d hd
    have := Nat.le_of_dvd (by omega : 0 < d) hdvd
    omega
  calc (∑ d ∈ F, ∏ p ∈ d.primeFactors, f p)
      = ∑ t ∈ F.image (fun d : ℕ => d.primeFactors), ∏ p ∈ t, f p := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ t ∈ P.powerset, ∏ p ∈ t, f p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro t ht _
        exact Finset.prod_nonneg (fun p hp =>
          hf p (Nat.prime_of_mem_primesBelow (Finset.mem_powerset.mp ht hp)))
    _ = ∏ p ∈ P, (1 + f p) := (Finset.prod_one_add P).symm

/-- Euler-product analytic bound: if `f` is nonnegative on primes and `f p ≤ C/p`,
then `∏_{p < N} (1 + f p)` is `O((log N)^C)`. -/
private lemma prod_one_add_le_logpow {f : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hf0 : ∀ p, p.Prime → 0 ≤ f p) (hfb : ∀ p, p.Prime → f p ≤ C / (p : ℝ)) :
    ∃ E : ℝ, 0 < E ∧ ∀ N : ℕ, 3 ≤ N →
      ∏ p ∈ Nat.primesBelow N, (1 + f p) ≤ E * (Real.log (N : ℝ)) ^ C := by
  obtain ⟨M, hMpos, hM⟩ := Commons.NumberTheory.Sieve.sum_primes_recip_le_loglog
  refine ⟨Real.exp (C * M), Real.exp_pos _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hsum : (∑ p ∈ Nat.primesBelow N, f p)
      ≤ C * (Real.log (Real.log (N : ℝ)) + M) := by
    have h1 : (∑ p ∈ Nat.primesBelow N, f p) ≤ ∑ p ∈ Nat.primesBelow N, C / (p : ℝ) :=
      Finset.sum_le_sum (fun p hp => hfb p (Nat.prime_of_mem_primesBelow hp))
    have h2 : (∑ p ∈ Nat.primesBelow N, C / (p : ℝ))
        = C * ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    have h3 := hM N hN2
    calc (∑ p ∈ Nat.primesBelow N, f p) ≤ ∑ p ∈ Nat.primesBelow N, C / (p : ℝ) := h1
      _ = C * ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / (p : ℝ) := h2
      _ ≤ C * (Real.log (Real.log (N : ℝ)) + M) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          linarith
  calc ∏ p ∈ Nat.primesBelow N, (1 + f p)
      ≤ ∏ p ∈ Nat.primesBelow N, Real.exp (f p) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have := hf0 p (Nat.prime_of_mem_primesBelow hp)
          linarith
        · intro p _hp
          have := Real.add_one_le_exp (f p)
          linarith
    _ = Real.exp (∑ p ∈ Nat.primesBelow N, f p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (C * (Real.log (Real.log (N : ℝ)) + M)) := Real.exp_le_exp.mpr hsum
    _ = Real.exp (C * Real.log (Real.log (N : ℝ))) * Real.exp (C * M) := by
        rw [show C * (Real.log (Real.log (N : ℝ)) + M)
              = C * Real.log (Real.log (N : ℝ)) + C * M by ring, Real.exp_add]
    _ = (Real.log (N : ℝ)) ^ C * Real.exp (C * M) := by
        congr 1
        rw [Real.rpow_def_of_pos hlogpos C]
        ring_nf
    _ = Real.exp (C * M) * (Real.log (N : ℝ)) ^ C := by ring

theorem sum_squarefree_tau_pow_mul_gdens_le {g : ℕ → ℝ}
    (hg0 : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hgp : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ)) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℕ, 2 ≤ x →
      (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ (20 / 3 : ℝ) * g d)
        ≤ C₀ * (Real.log (x : ℝ)) ^ K := by
  obtain ⟨C, hCpos, hCb⟩ := hgp
  by_cases hg1 : g 1 = 1
  · -- The multiplicative case.
    obtain ⟨M, _hMpos, hM⟩ := Commons.NumberTheory.Sieve.sum_primes_recip_le_loglog
    set α : ℝ := (2 : ℝ) ^ (20 / 3 : ℝ) with hα
    have hαpos : 0 < α := Real.rpow_pos_of_pos (by norm_num) _
    have hαnn : 0 ≤ α := hαpos.le
    obtain ⟨E, hEpos, hE⟩ := prod_one_add_le_logpow (f := fun p => α * g p)
      (C := α * C) (mul_pos hαpos hCpos)
      (fun p hp => mul_nonneg hαnn (hg0 p hp))
      (fun p hp => by
        have h := hCb p hp
        have h2 := mul_le_mul_of_nonneg_left h hαnn
        rw [mul_div_assoc]
        exact h2)
    refine ⟨(Real.log 2) ^ (-(α * C)) + E * 2 ^ (α * C), ?_, α * C,
      (mul_pos hαpos hCpos).le, ?_⟩
    · have h1 : 0 < (Real.log 2) ^ (-(α * C)) :=
        Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
      have h2 : 0 < E * 2 ^ (α * C) :=
        mul_pos hEpos (Real.rpow_pos_of_pos (by norm_num) _)
      linarith
    · intro x hx
      have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogxpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
      have hlogxnn : 0 ≤ Real.log (x : ℝ) := hlogxpos.le
      have hlog2le : Real.log 2 ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) hx2
      -- Rewrite the summand.
      have hterm : ∀ d ∈ (Finset.Icc 1 x).filter Squarefree,
          ((d.divisors.card : ℝ)) ^ (20 / 3 : ℝ) * g d
            = ∏ p ∈ d.primeFactors, (α * g p) := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, _⟩, hdsq⟩ := hd
        have hgd : g d = ∏ p ∈ d.primeFactors, g p :=
          Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors g hgmul hg1 hdsq
        rw [hgd, hα]
        exact term_eq_prod_rpow g hd1 hdsq
      rw [Finset.sum_congr rfl hterm]
      -- Euler product bound.
      have heuler := sum_sqfree_primeFactors_le_prod_euler (fun p => α * g p)
        (fun p hp => mul_nonneg hαnn (hg0 p hp)) x
      have hprod := hE (x + 1) (by omega)
      -- Comparison of logarithms.
      have hlog_y1_le : Real.log (((x + 1 : ℕ) : ℝ)) ≤ 2 * Real.log (x : ℝ) := by
        have hcast : (((x + 1 : ℕ) : ℝ)) = (x : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hle : (x : ℝ) + 1 ≤ (x : ℝ) ^ 2 := by nlinarith
        have h := Real.log_le_log (by linarith : (0 : ℝ) < (x : ℝ) + 1) hle
        rwa [Real.log_pow] at h
      have hlog_y1_nn : 0 ≤ Real.log (((x + 1 : ℕ) : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ x + 1 by omega))
      have hpow1 : (Real.log (((x + 1 : ℕ) : ℝ))) ^ (α * C) ≤ (2 * Real.log (x : ℝ)) ^ (α * C) :=
        Real.rpow_le_rpow hlog_y1_nn hlog_y1_le (mul_pos hαpos hCpos).le
      have hpow2 : (2 * Real.log (x : ℝ)) ^ (α * C)
          = (2 : ℝ) ^ (α * C) * (Real.log (x : ℝ)) ^ (α * C) :=
        Real.mul_rpow (by norm_num) hlogxnn
      have hmain : (Real.log 2) ^ (α * C) ≤ (Real.log (x : ℝ)) ^ (α * C) :=
        Real.rpow_le_rpow hlog2pos.le hlog2le (mul_pos hαpos hCpos).le
      have hkey : (1 : ℝ) ≤ (Real.log 2) ^ (-(α * C)) * (Real.log (x : ℝ)) ^ (α * C) := by
        have h1 : (Real.log 2) ^ (-(α * C)) * (Real.log 2) ^ (α * C) = 1 := by
          rw [← Real.rpow_add hlog2pos]
          norm_num
        rw [← h1]
        exact mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hlog2pos.le _)
      calc (∑ d ∈ (Finset.Icc 1 x).filter Squarefree, ∏ p ∈ d.primeFactors, (α * g p))
          ≤ ∏ p ∈ Nat.primesBelow (x + 1), (1 + α * g p) := heuler
        _ ≤ E * (Real.log (((x + 1 : ℕ) : ℝ))) ^ (α * C) := hprod
        _ ≤ E * (2 * Real.log (x : ℝ)) ^ (α * C) :=
              mul_le_mul_of_nonneg_left hpow1 hEpos.le
        _ = E * ((2 : ℝ) ^ (α * C) * (Real.log (x : ℝ)) ^ (α * C)) := by rw [hpow2]
        _ = E * 2 ^ (α * C) * (Real.log (x : ℝ)) ^ (α * C) := by ring
        _ ≤ ((Real.log 2) ^ (-(α * C)) + E * 2 ^ (α * C)) * (Real.log (x : ℝ)) ^ (α * C) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlogxnn _)
              linarith [Real.rpow_nonneg hlog2pos.le (-(α * C))]
  · -- The degenerate case `g 1 ≠ 1` forces `g ≡ 0`.
    have hg1z : g 1 = 0 := by
      have h := hgmul 1 1 (Nat.coprime_one_left 1)
      simp only [mul_one] at h
      have h2 : g 1 * (g 1 - 1) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd (by linarith) hg1
    have hgz : ∀ n : ℕ, g n = 0 := by
      intro n
      have h := hgmul 1 n (Nat.coprime_one_left n)
      simp only [one_mul] at h
      rw [h]
      simp [hg1z]
    refine ⟨1, one_pos, 0, le_refl 0, ?_⟩
    intro x _hx
    have hsum : (∑ d ∈ (Finset.Icc 1 x).filter Squarefree,
        ((d.divisors.card : ℝ)) ^ (20 / 3 : ℝ) * g d) = 0 := by
      apply Finset.sum_eq_zero
      intro d _hd
      rw [hgz d, mul_zero]
    rw [hsum, Real.rpow_zero]
    norm_num

end Commons.NumberTheory.Sieve
