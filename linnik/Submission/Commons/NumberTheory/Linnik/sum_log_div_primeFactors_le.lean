import Mathlib
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_div_prime_le_log

namespace Commons.NumberTheory.Linnik

open Finset

theorem sum_log_div_primeFactors_le :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 100 ≤ q →
      (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
        ≤ C * (Real.log (Real.log (q : ℝ)) + 2) ^ 2 := by
  refine ⟨1, one_pos, ?_⟩
  intro q hq
  have hq0 : q ≠ 0 := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  set L : ℝ := Real.log (q : ℝ) with hLdef
  -- Numeric facts about `L`.
  have hexp2 : Real.exp 2 < 100 := by
    have h4 : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    rw [h4]
    calc (Real.exp 1) ^ 2 < (3 : ℝ) ^ 2 :=
          pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
      _ < 100 := by norm_num
  have hlog100 : (2 : ℝ) < Real.log 100 := by
    have h := Real.log_lt_log (Real.exp_pos 2) hexp2
    rwa [Real.log_exp] at h
  have hL2 : 2 < L := by
    rw [hLdef]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 100)
      (by exact_mod_cast hq : (100 : ℝ) ≤ (q : ℝ))
    linarith
  have hLpos : 0 < L := by linarith
  have hhalf : (1 : ℝ) / 2 < Real.log L := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) hL2
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  set T : ℕ := ⌊L ^ 2⌋₊ with hTdef
  set B : Finset ℕ := q.primeFactors.filter (fun p => (p : ℝ) ≤ L ^ 2) with hBdef
  set A : Finset ℕ := q.primeFactors.filter (fun p => ¬ ((p : ℝ) ≤ L ^ 2)) with hAdef
  have hsplit : (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ))
      = (∑ p ∈ B, Real.log (p : ℝ) / (p : ℝ))
        + (∑ p ∈ A, Real.log (p : ℝ) / (p : ℝ)) := by
    rw [hAdef, hBdef]
    exact (Finset.sum_filter_add_sum_filter_not q.primeFactors
      (fun p : ℕ => (p : ℝ) ≤ L ^ 2) (fun p => Real.log (p : ℝ) / (p : ℝ))).symm
  -- Small-prime part.
  have hsub : B ⊆ T.primesLE := by
    intro p hp
    rw [hBdef, Finset.mem_filter] at hp
    obtain ⟨hpf, hple⟩ := hp
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hpf
    rw [Nat.mem_primesLE]
    refine ⟨?_, hpprime⟩
    rw [hTdef]
    exact Nat.le_floor hple
  have hnonneg : ∀ p ∈ T.primesLE, p ∉ B → 0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
    intro p hp _
    rw [Nat.mem_primesLE] at hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
      linarith
    exact div_nonneg (Real.log_nonneg hp1) (Nat.cast_nonneg p)
  have hsmall1 := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hT2 : (2 : ℝ) ≤ L ^ 2 := by nlinarith [hL2]
  have hmer := Commons.NumberTheory.Mertens.sum_log_prime_div_prime_le_log (L ^ 2) hT2
  have hmerT : (∑ p ∈ T.primesLE, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log (L ^ 2) := by
    rw [hTdef]; exact hmer
  have hlogL2 : Real.log (L ^ 2) = 2 * Real.log L :=
    Real.log_pow L 2
  have hsmall : (∑ p ∈ B, Real.log (p : ℝ) / (p : ℝ)) ≤ 2 * Real.log L := by
    linarith [hsmall1, hmerT, hlogL2]
  -- Large-prime part.
  have hA_sub : A ⊆ q.primeFactors := by rw [hAdef]; exact Finset.filter_subset _ _
  have hdvd_sub : ∏ p ∈ A, p ∣ ∏ p ∈ q.primeFactors, p := by
    have hsdiff := Finset.prod_sdiff hA_sub (f := fun p : ℕ => p)
    exact ⟨∏ x ∈ q.primeFactors \ A, x, by rw [mul_comm]; exact hsdiff.symm⟩
  have hdvd : ∏ p ∈ A, p ∣ q := hdvd_sub.trans (Nat.prod_primeFactors_dvd q)
  have hprod : ∏ p ∈ A, p ≤ q := Nat.le_of_dvd (by omega : 0 < q) hdvd
  have hprodpos : 0 < (∏ p ∈ A, p : ℕ) := Nat.pos_of_dvd_of_pos hdvd (by omega : 0 < q)
  have hlog_le : Real.log ((∏ p ∈ A, p : ℕ) : ℝ) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by exact_mod_cast hprodpos : (0:ℝ) < ((∏ p ∈ A, p : ℕ):ℝ))
      (by exact_mod_cast hprod : ((∏ p ∈ A, p : ℕ) : ℝ) ≤ (q : ℝ))
  have hlogeq : Real.log ((∏ p ∈ A, p : ℕ) : ℝ) = ∑ p ∈ A, Real.log (p : ℝ) := by
    push_cast
    rw [Real.log_prod]
    intro p hp
    rw [hAdef, Finset.mem_filter] at hp
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp.1
    exact_mod_cast (Nat.Prime.pos hpprime).ne'
  have hcard_log : (∑ p ∈ A, Real.log (L ^ 2)) = (A.card : ℝ) * Real.log (L ^ 2) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hpointwise : ∀ p ∈ A, Real.log (L ^ 2) ≤ Real.log (p : ℝ) := by
    intro p hp
    rw [hAdef, Finset.mem_filter] at hp
    exact le_of_lt (Real.log_lt_log (pow_pos hLpos 2) (not_le.mp hp.2))
  have hlower : (A.card : ℝ) * Real.log (L ^ 2) ≤ ∑ p ∈ A, Real.log (p : ℝ) := by
    rw [← hcard_log]; exact Finset.sum_le_sum hpointwise
  have hmul : (A.card : ℝ) * (2 * Real.log L) ≤ L := by
    have h := hlower.trans (le_of_eq hlogeq.symm)
    have := h.trans hlog_le
    rwa [hlogL2] at this
  have hterm : ∀ p ∈ A, Real.log (p : ℝ) / (p : ℝ) ≤ 1 / L := by
    intro p hp
    rw [hAdef, Finset.mem_filter] at hp
    obtain ⟨hpf, hnotle⟩ := hp
    have hlt : L ^ 2 < (p : ℝ) := not_le.mp hnotle
    rw [Nat.mem_primeFactors] at hpf
    obtain ⟨hpprime, hpdvd, _⟩ := hpf
    have hple : (p : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (Nat.le_of_dvd (by omega : 0 < q) hpdvd)
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos hpprime)
    have hlogp_le : Real.log (p : ℝ) ≤ L := by
      rw [hLdef]
      exact Real.log_le_log hp_pos hple
    have hkey : Real.log (p : ℝ) * L ≤ (p : ℝ) := by
      have h1 : Real.log (p : ℝ) * L ≤ L * L :=
        mul_le_mul_of_nonneg_right hlogp_le hLpos.le
      have h2 : L * L = L ^ 2 := by ring
      nlinarith [hlt, h1, h2]
    rw [div_le_iff₀ hp_pos, div_mul_eq_mul_div, le_div_iff₀ hLpos]
    linarith [hkey]
  have hsum_large : (∑ p ∈ A, Real.log (p : ℝ) / (p : ℝ)) ≤ (A.card : ℝ) * (1 / L) := by
    have := Finset.sum_le_card_nsmul A (fun p => Real.log (p : ℝ) / (p : ℝ)) (1 / L) hterm
    rwa [nsmul_eq_mul] at this
  have hge1 : (1 : ℝ) ≤ 2 * Real.log L := by linarith
  have hcard_le : (A.card : ℝ) ≤ L := by
    calc (A.card : ℝ) = (A.card : ℝ) * 1 := by ring
      _ ≤ (A.card : ℝ) * (2 * Real.log L) :=
          mul_le_mul_of_nonneg_left hge1 (Nat.cast_nonneg _)
      _ ≤ L := hmul
  have hlarge : (∑ p ∈ A, Real.log (p : ℝ) / (p : ℝ)) ≤ 1 := by
    calc (∑ p ∈ A, Real.log (p : ℝ) / (p : ℝ)) ≤ (A.card : ℝ) * (1 / L) := hsum_large
      _ ≤ L * (1 / L) := by
          apply mul_le_mul_of_nonneg_right hcard_le
          positivity
      _ = 1 := by rw [mul_one_div, div_self hLpos.ne']
  -- Combine.
  rw [hsplit]
  have hfinal : 2 * Real.log L + 1 ≤ (Real.log L + 2) ^ 2 := by
    nlinarith [sq_nonneg (Real.log L + 1)]
  linarith [hsmall, hlarge, hfinal]

end Commons.NumberTheory.Linnik
