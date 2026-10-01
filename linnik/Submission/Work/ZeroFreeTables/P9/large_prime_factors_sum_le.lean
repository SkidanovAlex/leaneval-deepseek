import Mathlib

namespace Work.ZeroFreeTables.P9

/-- Sum of `(log p)^j / p` over prime factors `p` of `q` exceeding `y` is at most
`(log q)^(j+1)/(y log y)`. -/
theorem large_prime_factors_sum_le (j q : ℕ) (hq : 1 ≤ q) (y : ℝ) (hy : 1 < y) :
    ∑ p ∈ q.primeFactors.filter (fun p : ℕ => y < (p : ℝ)), (Real.log (p : ℝ)) ^ j / (p : ℝ)
      ≤ (Real.log (q : ℝ)) ^ (j + 1) / (y * Real.log y) := by
  have hypos : 0 < y := lt_trans zero_lt_one hy
  have hlogy_pos : 0 < Real.log y := Real.log_pos hy
  have hylogy_pos : 0 < y * Real.log y := mul_pos hypos hlogy_pos
  -- Sum of the logs of the prime factors is at most `log q`.
  have hsum_log_le : ∑ p ∈ q.primeFactors, Real.log (p : ℝ) ≤ Real.log (q : ℝ) := by
    have hqpos : 0 < q := hq
    have hprod_pos : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp hp).1.pos)
    have hle : (∏ p ∈ q.primeFactors, p) ≤ q :=
      Nat.le_of_dvd hqpos (Nat.prod_primeFactors_dvd q)
    have h1 : ∑ p ∈ q.primeFactors, Real.log (p : ℝ)
        = Real.log ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      exact (Real.log_prod (fun p hp => by
        have hp' := (Nat.mem_primeFactors.mp hp).1
        exact_mod_cast hp'.ne_zero)).symm
    rw [h1]
    exact Real.log_le_log (by exact_mod_cast hprod_pos) (by exact_mod_cast hle)
  -- Termwise comparison with `(log p)^(j+1)/(y log y)`.
  have hterm : ∀ p ∈ q.primeFactors.filter (fun p : ℕ => y < (p : ℝ)),
      (Real.log (p : ℝ)) ^ j / (p : ℝ)
        ≤ (Real.log (p : ℝ)) ^ (j + 1) / (y * Real.log y) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpmem, hyp⟩ := hp
    have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hpmem).1
    have hppos : 0 < (p : ℝ) := by
      have : 2 ≤ p := hpprime.two_le
      exact_mod_cast (by omega : 0 < p)
    have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by
      have : 2 ≤ p := hpprime.two_le
      exact_mod_cast (by omega : 1 < p))
    have hylogp : y * Real.log y ≤ p * Real.log p := by
      have h1 : y * Real.log y ≤ p * Real.log y :=
        mul_le_mul_of_nonneg_right (le_of_lt hyp) (le_of_lt hlogy_pos)
      have h2 : Real.log y ≤ Real.log p := Real.log_le_log hypos (le_of_lt hyp)
      have h3 : p * Real.log y ≤ p * Real.log p :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt hppos)
      linarith
    rw [div_le_div_iff₀ hppos hylogy_pos]
    calc (Real.log (p : ℝ)) ^ j * (y * Real.log y)
        ≤ (Real.log (p : ℝ)) ^ j * (p * Real.log p) :=
          mul_le_mul_of_nonneg_left hylogp (pow_nonneg (le_of_lt hlogp_pos) j)
      _ = (Real.log (p : ℝ)) ^ (j + 1) * (p : ℝ) := by rw [pow_succ]; ring
  -- Bound on the sum of `(log p)^(j+1)`.
  have hbound : ∑ p ∈ q.primeFactors.filter (fun p : ℕ => y < (p : ℝ)),
        (Real.log (p : ℝ)) ^ (j + 1) ≤ (Real.log (q : ℝ)) ^ (j + 1) := by
    have hsub : q.primeFactors.filter (fun p : ℕ => y < (p : ℝ)) ⊆ q.primeFactors :=
      Finset.filter_subset _ _
    have hstep1 : ∑ p ∈ q.primeFactors.filter (fun p : ℕ => y < (p : ℝ)),
          (Real.log (p : ℝ)) ^ (j + 1)
        ≤ ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ (j + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
        pow_nonneg (Real.log_nonneg (by
          exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_le)) (j + 1))
    have hstep2 : ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ (j + 1)
        ≤ (Real.log (q : ℝ)) ^ (j + 1) := by
      have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
      have hterm2 : ∀ p ∈ q.primeFactors,
          (Real.log (p : ℝ)) ^ (j + 1) ≤ (Real.log (q : ℝ)) ^ j * Real.log (p : ℝ) := by
        intro p hp
        have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
        have hp_le_q : p ≤ q :=
          Nat.le_of_dvd hq (Nat.mem_primeFactors.mp hp).2.1
        have hlogp_nn : 0 ≤ Real.log (p : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hpprime.one_le)
        have hlogp_le : Real.log (p : ℝ) ≤ Real.log (q : ℝ) :=
          Real.log_le_log (by exact_mod_cast hpprime.pos) (by exact_mod_cast hp_le_q)
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlogp_nn hlogp_le j) hlogp_nn
      calc ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ (j + 1)
          ≤ ∑ p ∈ q.primeFactors, (Real.log (q : ℝ)) ^ j * Real.log (p : ℝ) :=
            Finset.sum_le_sum hterm2
        _ = (Real.log (q : ℝ)) ^ j * ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ (Real.log (q : ℝ)) ^ j * Real.log (q : ℝ) :=
            mul_le_mul_of_nonneg_left hsum_log_le (pow_nonneg hlogq_nn j)
        _ = (Real.log (q : ℝ)) ^ (j + 1) := by rw [pow_succ]
    exact le_trans hstep1 hstep2
  calc ∑ p ∈ q.primeFactors.filter (fun p : ℕ => y < (p : ℝ)),
          (Real.log (p : ℝ)) ^ j / (p : ℝ)
      ≤ ∑ p ∈ q.primeFactors.filter (fun p : ℕ => y < (p : ℝ)),
          (Real.log (p : ℝ)) ^ (j + 1) / (y * Real.log y) := Finset.sum_le_sum hterm
    _ = (∑ p ∈ q.primeFactors.filter (fun p : ℕ => y < (p : ℝ)),
          (Real.log (p : ℝ)) ^ (j + 1)) / (y * Real.log y) := by rw [Finset.sum_div]
    _ ≤ (Real.log (q : ℝ)) ^ (j + 1) / (y * Real.log y) :=
        div_le_div_of_nonneg_right hbound (le_of_lt hylogy_pos)

end Work.ZeroFreeTables.P9
