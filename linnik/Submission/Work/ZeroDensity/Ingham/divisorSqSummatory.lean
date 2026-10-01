import Mathlib
import Submission.Work.ZeroDensity.Montgomery.divisorsCardDivSum_le
import Submission.Work.ZeroDensity.Montgomery.cardDivisorsSq_eq_sum
import Submission.Work.ZeroDensity.Montgomery.twoPowOmegaDivSum_le

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

/-- Reindexing a double sum over divisors:
`∑_{n ≤ N} ∑_{d ∣ n} F d (n/d) = ∑_{d ≤ N} ∑_{m ≤ N/d} F d m`. -/
private lemma sum_divisors_reindex (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors, F d (n / d)
      = ∑ d ∈ Finset.Ioc 0 N, ∑ m ∈ Finset.Ioc 0 (N / d), F d m := by
  have key : (∑ x ∈ (Finset.Ioc 0 N).sigma (fun n => n.divisors), F x.2 (x.1 / x.2))
      = ∑ y ∈ (Finset.Ioc 0 N).sigma (fun d => Finset.Ioc 0 (N / d)), F y.1 y.2 := by
    refine Finset.sum_bij (fun x _ => (⟨x.2, x.1 / x.2⟩ : Sigma (fun _ : ℕ => ℕ))) ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨n, d⟩ := x
      obtain ⟨hn, hd⟩ := Finset.mem_sigma.mp hx
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · exact Finset.mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors hd,
          le_trans (Nat.divisor_le hd) (Finset.mem_Ioc.mp hn).2⟩
      · exact Finset.mem_Ioc.mpr ⟨Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd),
          Nat.div_le_div_right (Finset.mem_Ioc.mp hn).2⟩
    · intro x hx x' hx' h
      obtain ⟨n, d⟩ := x
      obtain ⟨n', d'⟩ := x'
      obtain ⟨hn, hd⟩ := Finset.mem_sigma.mp hx
      obtain ⟨hn', hd'⟩ := Finset.mem_sigma.mp hx'
      have h1 : d = d' := by injection h
      have h2 : n / d = n' / d' := by injection h
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hdvd' : d' ∣ n' := (Nat.mem_divisors.mp hd').1
      have hn : n = n' := by
        calc n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
          _ = d' * (n' / d') := by rw [h2, h1]
          _ = n' := Nat.mul_div_cancel' hdvd'
      rw [hn, h1]
    · intro y hy
      obtain ⟨d, m⟩ := y
      obtain ⟨hd, hm⟩ := Finset.mem_sigma.mp hy
      have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
      have hm0 : 0 < m := (Finset.mem_Ioc.mp hm).1
      have hmul : d * m ≤ N := by
        rw [Nat.mul_comm]
        exact (Nat.le_div_iff_mul_le hd0).mp (Finset.mem_Ioc.mp hm).2
      refine ⟨⟨d * m, d⟩, ?_, ?_⟩
      · refine Finset.mem_sigma.mpr ⟨Finset.mem_Ioc.mpr ⟨Nat.mul_pos hd0 hm0, hmul⟩, ?_⟩
        exact Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right d m, (Nat.mul_pos hd0 hm0).ne'⟩
      · show (⟨d, d * m / d⟩ : Sigma (fun _ : ℕ => ℕ)) = ⟨d, m⟩
        rw [Nat.mul_div_cancel_left m hd0]
    · intro x hx
      rfl
  rw [Finset.sum_sigma', Finset.sum_sigma', key]

/-- `∑_{m ≤ M} τ(m) ≤ M (1 + log M)` (elementary harmonic estimate for the divisor function). -/
private lemma sum_tau_le (M : ℕ) :
    ∑ m ∈ Finset.Ioc 0 M, ((m.divisors.card : ℝ))
      ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) := by
  have hstep : ∑ m ∈ Finset.Ioc 0 M, ((m.divisors.card : ℝ))
      = ∑ m ∈ Finset.Ioc 0 M, ∑ d ∈ m.divisors, (1 : ℝ) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hstep, sum_divisors_reindex M (fun _ _ => (1 : ℝ))]
  have hcard : ∀ d : ℕ, (∑ m ∈ Finset.Ioc 0 (M / d), (1 : ℝ)) = ((M / d : ℕ) : ℝ) := by
    intro d
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc, Nat.sub_zero]
  simp_rw [hcard]
  calc ∑ d ∈ Finset.Ioc 0 M, ((M / d : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Ioc 0 M, (M : ℝ) / (d : ℝ) :=
        Finset.sum_le_sum (fun d _ => Nat.cast_div_le)
    _ = (M : ℝ) * ∑ d ∈ Finset.Ioc 0 M, 1 / (d : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun d _ => by ring)
    _ ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Work.ZeroDensity.Montgomery.sum_Ioc_inv_le_one_add_log M) (Nat.cast_nonneg M)

/-- **Summatory bound for the square of the divisor function**: for `N ≥ 1`,
`∑_{n ≤ N} τ(n)² ≤ C N (log 2N)³` with `C` absolute. -/
theorem divisorSqSummatory : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 1 N, (((Nat.divisors n).card : ℝ)) ^ 2
      ≤ C * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ 3 := by
  refine ⟨27, by norm_num, ?_⟩
  intro N hN
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc]
  have hstep : ∑ n ∈ Finset.Ioc 0 N, (((Nat.divisors n).card : ℝ)) ^ 2
      = ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ n.divisors,
          (2 : ℝ) ^ d.primeFactors.card * ((n / d).divisors.card : ℝ) :=
    Finset.sum_congr rfl (fun n _ => Work.ZeroDensity.Montgomery.cardDivisorsSq_eq_sum n)
  rw [hstep, sum_divisors_reindex N
    (fun d m => (2 : ℝ) ^ d.primeFactors.card * (m.divisors.card : ℝ))]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hinner : ∀ d ∈ Finset.Ioc 0 N,
      (∑ m ∈ Finset.Ioc 0 (N / d),
          (2 : ℝ) ^ d.primeFactors.card * ((m.divisors.card : ℝ)))
        ≤ (2 : ℝ) ^ d.primeFactors.card * ((N : ℝ) / (d : ℝ)) * (1 + Real.log (N : ℝ)) := by
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hτ : (∑ m ∈ Finset.Ioc 0 (N / d), ((m.divisors.card : ℝ)))
        ≤ ((N / d : ℕ) : ℝ) * (1 + Real.log ((N / d : ℕ) : ℝ)) := sum_tau_le (N / d)
    have hcast : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hlogN : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
      rcases Nat.eq_zero_or_pos (N / d) with h | h
      · simpa [h] using hlogN0
      · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.div_le_self N d)
    have h1log : (0 : ℝ) ≤ 1 + Real.log ((N / d : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos (N / d) with h | h
      · simp [h]
      · have h1 : (1 : ℝ) ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast h
        have := Real.log_nonneg h1
        linarith
    have hstep2 : ((N / d : ℕ) : ℝ) * (1 + Real.log ((N / d : ℕ) : ℝ))
        ≤ ((N : ℝ) / (d : ℝ)) * (1 + Real.log (N : ℝ)) :=
      mul_le_mul hcast (by linarith) h1log (by positivity)
    have hchain : (∑ m ∈ Finset.Ioc 0 (N / d), ((m.divisors.card : ℝ)))
        ≤ ((N : ℝ) / (d : ℝ)) * (1 + Real.log (N : ℝ)) := hτ.trans hstep2
    rw [← Finset.mul_sum]
    calc (2 : ℝ) ^ d.primeFactors.card
          * (∑ m ∈ Finset.Ioc 0 (N / d), ((m.divisors.card : ℝ)))
        ≤ (2 : ℝ) ^ d.primeFactors.card
            * (((N : ℝ) / (d : ℝ)) * (1 + Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hchain (by positivity)
      _ = (2 : ℝ) ^ d.primeFactors.card * ((N : ℝ) / (d : ℝ))
            * (1 + Real.log (N : ℝ)) := by ring
  calc ∑ d ∈ Finset.Ioc 0 N, ∑ m ∈ Finset.Ioc 0 (N / d),
        (2 : ℝ) ^ d.primeFactors.card * ((m.divisors.card : ℝ))
      ≤ ∑ d ∈ Finset.Ioc 0 N,
          (2 : ℝ) ^ d.primeFactors.card * ((N : ℝ) / (d : ℝ))
            * (1 + Real.log (N : ℝ)) :=
        Finset.sum_le_sum hinner
    _ = (N : ℝ) * (1 + Real.log (N : ℝ))
          * ∑ d ∈ Finset.Ioc 0 N, (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun d _ => by ring)
    _ ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Work.ZeroDensity.Montgomery.twoPowOmegaDivSum_le N) (by positivity)
    _ ≤ 27 * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ 3 := by
        have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        have hmul : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) :=
          Real.log_mul (by norm_num) (by positivity)
        have hle : 1 + Real.log (N : ℝ) ≤ 3 * Real.log (2 * (N : ℝ)) := by
          rw [hmul]; nlinarith
        have hpow : (1 + Real.log (N : ℝ)) ^ 3
            ≤ (3 * Real.log (2 * (N : ℝ))) ^ 3 := pow_le_pow_left₀ (by linarith) hle 3
        calc (N : ℝ) * (1 + Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) ^ 2
            = (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by ring
          _ ≤ (N : ℝ) * (3 * Real.log (2 * (N : ℝ))) ^ 3 :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = 27 * (N : ℝ) * (Real.log (2 * (N : ℝ))) ^ 3 := by ring

end Work.ZeroDensity.Ingham
