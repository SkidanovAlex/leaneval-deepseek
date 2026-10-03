import Mathlib
import Submission.Commons.NumberTheory.Nat.sum_log_primeFactors_le_log
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_div_prime_le_log

namespace Commons.NumberTheory.Sieve

/-- For a prime `p` dividing `ν`, `p / gcd ν p = 1`. -/
private lemma prime_div_gcd_eq_one {p ν : ℕ} (hpp : p.Prime) (h : p ∣ ν) :
    p / Nat.gcd ν p = 1 := by
  rw [Nat.gcd_eq_right h, Nat.div_self hpp.pos]

/-- For a prime `p` not dividing `ν`, `p / gcd ν p = p`. -/
private lemma prime_div_gcd_eq_self {p ν : ℕ} (hpp : p.Prime) (h : ¬ p ∣ ν) :
    p / Nat.gcd ν p = p := by
  have hcop : ν.Coprime p := (hpp.coprime_iff_not_dvd.mpr h).symm
  rw [hcop.gcd_eq_one, Nat.div_one]

theorem sum_primes_log_mul_g_div_gcd_le {g : ℕ → ℝ}
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν z : ℕ, Squarefree ν → 2 ≤ z →
      (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Real.log (p : ℝ) * g (p / Nat.gcd ν p))
        ≤ C * Real.log ((ν : ℝ) * (z : ℝ) + 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := hbound
  refine ⟨max (g 1) 0 + C0, ?_, ?_⟩
  · have := le_max_right (g 1) 0
    linarith
  · intro ν z hsf hz
    set T : Finset ℕ := (Finset.Icc 1 z).filter Nat.Prime with hT
    have hmem : ∀ p ∈ T, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
    have hge : ∀ p ∈ T, 1 ≤ p :=
      fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hnu0 : ν ≠ 0 := hsf.ne_zero
    have hnu1 : 1 ≤ ν := Nat.one_le_iff_ne_zero.mpr hnu0
    -- step 1: pointwise bound for the summand
    have hterm : ∀ p ∈ T, Real.log (p : ℝ) * g (p / Nat.gcd ν p)
        ≤ (if p ∣ ν then max (g 1) 0 * Real.log (p : ℝ)
            else C0 * (Real.log (p : ℝ) / (p : ℝ))) := by
      intro p hpT
      have hpp : p.Prime := hmem p hpT
      have hp1 : 1 ≤ p := hge p hpT
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
      by_cases h : p ∣ ν
      · rw [if_pos h, prime_div_gcd_eq_one hpp h]
        calc Real.log (p : ℝ) * g 1
            ≤ Real.log (p : ℝ) * max (g 1) 0 :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) hlog
          _ = max (g 1) 0 * Real.log (p : ℝ) := by ring
      · rw [if_neg h, prime_div_gcd_eq_self hpp h]
        have hgp := hC0 p hpp
        have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
        calc Real.log (p : ℝ) * g p
            ≤ Real.log (p : ℝ) * (C0 / (p : ℝ)) :=
              mul_le_mul_of_nonneg_left hgp hlog
          _ = C0 * (Real.log (p : ℝ) / (p : ℝ)) := by
              field_simp
    have hstep1 : (∑ p ∈ T, Real.log (p : ℝ) * g (p / Nat.gcd ν p))
        ≤ ∑ p ∈ T, (if p ∣ ν then max (g 1) 0 * Real.log (p : ℝ)
            else C0 * (Real.log (p : ℝ) / (p : ℝ))) :=
      Finset.sum_le_sum hterm
    have hstep2 : (∑ p ∈ T, (if p ∣ ν then max (g 1) 0 * Real.log (p : ℝ)
            else C0 * (Real.log (p : ℝ) / (p : ℝ))))
        = (∑ p ∈ T.filter (fun p => p ∣ ν), max (g 1) 0 * Real.log (p : ℝ))
          + ∑ p ∈ T.filter (fun p => ¬ p ∣ ν),
              C0 * (Real.log (p : ℝ) / (p : ℝ)) :=
      Finset.sum_ite _ _
    -- bound the "divides" part
    have hA : (∑ p ∈ T.filter (fun p => p ∣ ν), max (g 1) 0 * Real.log (p : ℝ))
        ≤ max (g 1) 0 * Real.log ((ν : ℝ) * (z : ℝ) + 2) := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (le_max_right (g 1) 0)
      have hsub : T.filter (fun p => p ∣ ν) ⊆ ν.primeFactors := by
        intro p hp
        rw [Finset.mem_filter] at hp
        exact Nat.mem_primeFactors.mpr ⟨hmem p hp.1, hp.2, hnu0⟩
      have hnonneg : ∀ x ∈ ν.primeFactors, x ∉ T.filter (fun p => p ∣ ν) →
          0 ≤ Real.log (x : ℝ) := by
        intro x hx _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primeFactors.mp hx).1.one_le)
      have h1 : (∑ p ∈ T.filter (fun p => p ∣ ν), Real.log (p : ℝ))
          ≤ ∑ p ∈ ν.primeFactors, Real.log (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      have h2 : (∑ p ∈ ν.primeFactors, Real.log (p : ℝ)) ≤ Real.log (ν : ℝ) :=
        Commons.NumberTheory.Nat.sum_log_primeFactors_le_log ν
      have h3 : Real.log (ν : ℝ) ≤ Real.log ((ν : ℝ) * (z : ℝ) + 2) := by
        refine Real.log_le_log ?_ ?_
        · exact_mod_cast (Nat.pos_of_ne_zero hnu0)
        · have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
          have hνnn : (0 : ℝ) ≤ (ν : ℝ) := Nat.cast_nonneg ν
          nlinarith
      linarith
    -- bound the "not divides" part
    have hB : (∑ p ∈ T.filter (fun p => ¬ p ∣ ν),
          C0 * (Real.log (p : ℝ) / (p : ℝ)))
        ≤ C0 * Real.log ((ν : ℝ) * (z : ℝ) + 2) := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC0pos)
      have hsub : T.filter (fun p => ¬ p ∣ ν) ⊆ Nat.primesLE z := by
        intro p hp
        rw [Finset.mem_filter] at hp
        exact Nat.mem_primesLE.mpr
          ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hp.1).1).2, hmem p hp.1⟩
      have hnonneg : ∀ x ∈ Nat.primesLE z, x ∉ T.filter (fun p => ¬ p ∣ ν) →
          0 ≤ Real.log (x : ℝ) / (x : ℝ) := by
        intro x hx _
        have hxp : x.Prime := (Nat.mem_primesLE.mp hx).2
        have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxp.pos
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hxp.one_le)) (le_of_lt hx0)
      have h1 : (∑ p ∈ T.filter (fun p => ¬ p ∣ ν), Real.log (p : ℝ) / (p : ℝ))
          ≤ ∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      have h2 : (∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) / (p : ℝ))
          ≤ Real.log (z : ℝ) := by
        have h := Commons.NumberTheory.Mertens.sum_log_prime_div_prime_le_log
          (z : ℝ) (by exact_mod_cast hz)
        rwa [Nat.floor_natCast] at h
      have h3 : Real.log (z : ℝ) ≤ Real.log ((ν : ℝ) * (z : ℝ) + 2) := by
        refine Real.log_le_log (by positivity) ?_
        have hνR : (1 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hnu1
        have hzR : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
        nlinarith
      linarith
    have htotal : (∑ p ∈ T, Real.log (p : ℝ) * g (p / Nat.gcd ν p))
        ≤ max (g 1) 0 * Real.log ((ν : ℝ) * (z : ℝ) + 2)
          + C0 * Real.log ((ν : ℝ) * (z : ℝ) + 2) := by
      calc (∑ p ∈ T, Real.log (p : ℝ) * g (p / Nat.gcd ν p))
          ≤ ∑ p ∈ T, (if p ∣ ν then max (g 1) 0 * Real.log (p : ℝ)
              else C0 * (Real.log (p : ℝ) / (p : ℝ))) := hstep1
        _ = (∑ p ∈ T.filter (fun p => p ∣ ν), max (g 1) 0 * Real.log (p : ℝ))
              + ∑ p ∈ T.filter (fun p => ¬ p ∣ ν),
                  C0 * (Real.log (p : ℝ) / (p : ℝ)) := hstep2
        _ ≤ max (g 1) 0 * Real.log ((ν : ℝ) * (z : ℝ) + 2)
              + C0 * Real.log ((ν : ℝ) * (z : ℝ) + 2) := add_le_add hA hB
    have : max (g 1) 0 * Real.log ((ν : ℝ) * (z : ℝ) + 2)
          + C0 * Real.log ((ν : ℝ) * (z : ℝ) + 2)
        = (max (g 1) 0 + C0) * Real.log ((ν : ℝ) * (z : ℝ) + 2) := by ring
    linarith [htotal, this]

end Commons.NumberTheory.Sieve
