import Mathlib
import Submission.Work.LinnikAreas.Density4.dtb_sum_Icc_inv_pm1_rpow_le_four

namespace Work.LinnikAreas.Density4

/-- The Euler-type product `∏_{p | r} (1 + 1/(p-1)^{3/2})` over the distinct prime
divisors of `r` is bounded by the absolute constant `1000`.

We bound each factor by its exponential (`1 + x ≤ e ^ x`), so the product is at most
`e ^ (Σ_{p|r} 1/(p-1)^{3/2})`; the exponent is a partial tail of `Σ_{m≥1} m^{-3/2}`,
which is at most `4`, and `e ^ 4 ≤ 1000`. -/
theorem dtb_prod_B_le (r : ℕ) (hr : 1 ≤ r) :
    (∏ p ∈ r.primeFactors, (1 + 1 / ((p : ℝ) - 1) ^ (3 / 2 : ℝ))) ≤ 1000 := by
  have h2 : ∀ p ∈ r.primeFactors, 2 ≤ p :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  -- Step 1: bound the product by `exp` of the sum of the same terms.
  have hprod : (∏ p ∈ r.primeFactors, (1 + 1 / ((p : ℝ) - 1) ^ (3 / 2 : ℝ)))
      ≤ Real.exp (∑ p ∈ r.primeFactors, 1 / ((p : ℝ) - 1) ^ (3 / 2 : ℝ)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro p hp
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast h2 p hp
      have : (0:ℝ) < (p:ℝ) - 1 := by linarith
      positivity
    · intro p hp
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast h2 p hp
      have h1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
      have hx : 0 ≤ 1 / ((p : ℝ) - 1) ^ (3/2 : ℝ) := by positivity
      linarith [Real.add_one_le_exp (1 / ((p : ℝ) - 1) ^ (3/2 : ℝ))]
  -- Step 2: transfer the sum over the prime factors to the full range `2 ≤ n ≤ r`.
  have hsub : (∑ p ∈ r.primeFactors, 1 / ((p:ℝ) - 1) ^ (3/2:ℝ))
      ≤ (∑ n ∈ Finset.Icc 2 r, 1 / ((n:ℝ) - 1) ^ (3/2:ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_Icc]
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      exact ⟨hpp.two_le, Nat.le_of_dvd (by omega) (Nat.mem_primeFactors.mp hp).2.1⟩
    · intro n hn hnmem
      have hn2 : (2:ℝ) ≤ (n:ℝ) := by
        have : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        exact_mod_cast this
      have : (0:ℝ) < (n:ℝ) - 1 := by linarith
      positivity
  have hsum : (∑ p ∈ r.primeFactors, 1 / ((p:ℝ) - 1) ^ (3/2:ℝ)) ≤ 4 :=
    hsub.trans (dtb_sum_Icc_inv_pm1_rpow_le_four r)
  -- Step 3: `e ^ 4 ≤ 1000`.
  have hexp4 : Real.exp 4 ≤ 1000 := by
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
      have h := Real.exp_nat_mul (1:ℝ) 4
      simpa only [Nat.cast_ofNat, mul_one] using h
    rw [h4]
    have hlt : Real.exp 1 ^ 4 < (3:ℝ)^4 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
    norm_num at hlt
    linarith
  calc (∏ p ∈ r.primeFactors, (1 + 1 / ((p : ℝ) - 1) ^ (3 / 2 : ℝ)))
      ≤ Real.exp (∑ p ∈ r.primeFactors, 1 / ((p : ℝ) - 1) ^ (3 / 2 : ℝ)) := hprod
    _ ≤ Real.exp 4 := Real.exp_le_exp.mpr hsum
    _ ≤ 1000 := hexp4

end Work.LinnikAreas.Density4
