import Mathlib
import Submission.Commons.NumberTheory.PrimeReciprocals.prime_product_inc_le_log

namespace Commons.NumberTheory.Sieve

open scoped BigOperators

/-- Euler-product style bound: `∏_{p < z, p prime} (1 + 1/p) = O(log z)` for `z ≥ 2`.

For `z ≥ 5` this follows from the Euler–Mertens estimate for the sum of `1/p`
(`Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log`) together with
`1 + x ≤ exp x`.  The finitely many small values `z ≤ 4` are handled by the crude
bound `∏ (1 + 1/p) ≤ 2 ^ #(primesBelow z) ≤ 2 ^ 4`. -/
theorem prod_one_add_inv_prime_le_log_of_two_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 2 ≤ z →
      (∏ p ∈ Nat.primesBelow z, (1 + 1 / (p : ℝ))) ≤ C * Real.log z := by
  rcases Commons.NumberTheory.PrimeReciprocals.prime_recip_sum_le_log_log with ⟨A, _hA0, hA⟩
  refine ⟨max (Real.exp A) 32, lt_max_of_lt_left (Real.exp_pos A), ?_⟩
  intro z hz
  -- `log z ≥ 1/2` for `z ≥ 2`
  have hlogz_half : (1 : ℝ) / 2 ≤ Real.log (z : ℝ) := by
    have h2z : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact le_trans hlog2 (Real.log_le_log (by norm_num) h2z)
  have hlogz_nonneg : 0 ≤ Real.log (z : ℝ) := by linarith
  rcases lt_or_ge z 5 with hz5lt | hz5
  · -- small `z`: bound the product crudely by `2 ^ #(primesBelow z) ≤ 16`
    have hprod : (∏ p ∈ Nat.primesBelow z, (1 + 1 / (p : ℝ))) ≤ 16 := by
      calc (∏ p ∈ Nat.primesBelow z, (1 + 1 / (p : ℝ)))
          ≤ ∏ _p ∈ Nat.primesBelow z, (2 : ℝ) := by
            refine Finset.prod_le_prod₀ ?_ ?_
            · intro p hp
              have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
              have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
              have : (0 : ℝ) < 1 / (p : ℝ) := by positivity
              linarith
            · intro p hp
              have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
              have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
              have hle : (1 : ℝ) / (p : ℝ) ≤ 1 := by
                rw [div_le_one hp0]
                exact_mod_cast (by omega : 1 ≤ p)
              linarith
        _ = (2 : ℝ) ^ (Nat.primesBelow z).card := Finset.prod_const (2 : ℝ)
        _ ≤ 16 := by
            have hsub : Nat.primesBelow z ⊆ Finset.range z := fun p hp =>
              Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp)
            have hcard : (Nat.primesBelow z).card ≤ 4 := by
              have hlt5 : z < 5 := hz5lt
              have := Finset.card_le_card hsub
              simp only [Finset.card_range] at this
              omega
            have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hcard
            norm_num at h
            exact h
    have hmul : (16 : ℝ) ≤ max (Real.exp A) 32 * Real.log (z : ℝ) := by
      have h32 : (32 : ℝ) ≤ max (Real.exp A) 32 := le_max_right _ _
      have h := mul_le_mul h32 hlogz_half (by norm_num) (by positivity)
      linarith
    linarith
  · -- large `z` (`z ≥ 5`): Euler product vs. exponential of the reciprocal sum
    have hN3 : 3 ≤ z - 1 := by omega
    have hN1 : z - 1 + 1 = z := by omega
    have hNpos : (0 : ℝ) < ((z - 1 : ℕ) : ℝ) := by
      have : 0 < z - 1 := by omega
      exact_mod_cast this
    have hlogNpos : 0 < Real.log (((z - 1 : ℕ)) : ℝ) := by
      have h2N : (2 : ℝ) ≤ ((z - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 ≤ z - 1)
      exact lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2))
        (Real.log_le_log (by norm_num) h2N)
    have hsum := hA (z - 1) hN3
    rw [hN1] at hsum
    have hlogNle : Real.log (((z - 1 : ℕ)) : ℝ) ≤ Real.log (z : ℝ) := by
      refine Real.log_le_log hNpos ?_
      exact_mod_cast (by omega : z - 1 ≤ z)
    calc (∏ p ∈ Nat.primesBelow z, (1 + 1 / (p : ℝ)))
        ≤ ∏ p ∈ Nat.primesBelow z, Real.exp (1 / (p : ℝ)) := by
          refine Finset.prod_le_prod₀ ?_ ?_
          · intro p hp
            have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
            have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
            have : (0 : ℝ) < 1 / (p : ℝ) := by positivity
            linarith
          · intro p hp
            simpa [add_comm] using Real.add_one_le_exp (1 / (p : ℝ))
      _ = Real.exp (∑ p ∈ Nat.primesBelow z, 1 / (p : ℝ)) :=
          (Real.exp_sum (Nat.primesBelow z) (fun p : ℕ => 1 / (p : ℝ))).symm
      _ ≤ Real.exp (A + Real.log (Real.log (((z - 1 : ℕ)) : ℝ))) :=
          Real.exp_le_exp.mpr hsum
      _ = Real.exp A * Real.log (((z - 1 : ℕ)) : ℝ) := by
          rw [Real.exp_add, Real.exp_log hlogNpos]
      _ ≤ max (Real.exp A) 32 * Real.log (z : ℝ) := by
          have hEA : Real.exp A ≤ max (Real.exp A) 32 := le_max_left _ _
          calc Real.exp A * Real.log (((z - 1 : ℕ)) : ℝ)
              ≤ Real.exp A * Real.log (z : ℝ) :=
                mul_le_mul_of_nonneg_left hlogNle (Real.exp_pos A).le
            _ ≤ max (Real.exp A) 32 * Real.log (z : ℝ) :=
                mul_le_mul_of_nonneg_right hEA hlogz_nonneg

end Commons.NumberTheory.Sieve
