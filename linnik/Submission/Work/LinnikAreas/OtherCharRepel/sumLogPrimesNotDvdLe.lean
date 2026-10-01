import Mathlib

namespace Work.LinnikAreas.OtherCharRepel

/-- The sum of the logarithms of the primes dividing `q` but not `N` is at most
`log q - log N`, whenever `N` divides `q` (and both are nonzero). -/
theorem sumLogPrimesNotDvdLe (N q : ℕ) [NeZero N] [NeZero q] (hdvd : N ∣ q) :
    ∑ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ N), Real.log (p : ℝ) ≤
      Real.log (q : ℝ) - Real.log (N : ℝ) := by
  have hq : q ≠ 0 := NeZero.ne q
  have hN : N ≠ 0 := NeZero.ne N
  set T := q.primeFactors.filter (fun p => ¬ p ∣ N) with hT
  have hsub : T ⊆ q.primeFactors := by
    rw [hT]; exact Finset.filter_subset _ _
  -- the product of the "extra" primes divides q
  have hdvdq : (∏ p ∈ T, p) ∣ q :=
    (Finset.prod_dvd_prod_of_subset T q.primeFactors (fun p => p) hsub).trans
      (Nat.prod_primeFactors_dvd q)
  have hmemb : ∀ p ∈ T, p.Prime ∧ p ∣ q := by
    intro p hp
    have hpq := hsub hp
    exact ⟨Nat.prime_of_mem_primeFactors hpq, (Nat.mem_primeFactors.mp hpq).2.1⟩
  have hnotN : ∀ p ∈ T, ¬ p ∣ N := by
    intro p hp
    rw [hT] at hp
    exact (Finset.mem_filter.mp hp).2
  -- ... and it is coprime to N, so it divides q / N
  have hcop : (∏ p ∈ T, p).Coprime N := by
    apply Nat.Coprime.prod_left
    intro p hp
    exact ((hmemb p hp).1.coprime_iff_not_dvd).2 (hnotN p hp)
  have hdvdm : (∏ p ∈ T, p) ∣ q / N := by
    have h1 : (∏ p ∈ T, p) ∣ N * (q / N) := by
      rw [← Nat.mul_div_cancel' hdvd] at hdvdq
      exact hdvdq
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop h1
  have hmpos : 0 < q / N :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdvd) (Nat.pos_of_ne_zero hN)
  have hle : (∏ p ∈ T, p) ≤ q / N := Nat.le_of_dvd hmpos hdvdm
  -- take logarithms
  have hdpos : 0 < (∏ p ∈ T, p : ℕ) :=
    Finset.prod_pos fun p hp => (hmemb p hp).1.pos
  have hlog : Real.log ((∏ p ∈ T, p : ℕ) : ℝ) = ∑ p ∈ T, Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (hmemb p hp).1.ne_zero
  rw [← hlog]
  have hcast : ((q / N : ℕ) : ℝ) = (q : ℝ) / (N : ℝ) := Nat.cast_div_charZero hdvd
  calc Real.log ((∏ p ∈ T, p : ℕ) : ℝ)
      ≤ Real.log ((q / N : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hdpos) (by exact_mod_cast hle)
    _ = Real.log ((q : ℝ) / (N : ℝ)) := by rw [hcast]
    _ = Real.log (q : ℝ) - Real.log (N : ℝ) :=
        Real.log_div (by exact_mod_cast hq) (by exact_mod_cast hN)

end Work.LinnikAreas.OtherCharRepel
