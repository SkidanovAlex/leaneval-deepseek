import Mathlib
import Submission.Work.ZeroDensity.Montgomery.divisorSqSum

namespace Work.ZeroDensity.Ingham

/-- **Weighted divisor-square summatory bound with a cube.** For `L ≥ 1`,
`∑_{n ≤ L} τ(n)² (1 + log n)³ / n ≤ C (log 2L)⁷`, where `τ(n) = (Nat.divisors n).card`.

This follows from the weighted second moment `∑_{n ≤ L} τ(n)²/n ≤ C₀ (log 2L)⁴`
(`Work.ZeroDensity.Montgomery.divisorSqSum`) together with the pointwise bound
`1 + log n ≤ 1 + log L ≤ 2 log (2L)` for `1 ≤ n ≤ L`. -/
theorem tauSqLogWeightedSummatory : ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L →
    (∑ n ∈ Finset.Icc 1 L,
        ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹)
      ≤ C * (Real.log (2 * (L : ℝ))) ^ 7 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.ZeroDensity.Montgomery.divisorSqSum
  refine ⟨8 * C₀, by positivity, ?_⟩
  intro L hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hlogL_nn : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmul : Real.log (2 * (L : ℝ)) = Real.log 2 + Real.log (L : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hLpos)
  have hbase : 0 ≤ 1 + Real.log (L : ℝ) := by linarith
  have hlog2L_nn : 0 ≤ Real.log (2 * (L : ℝ)) := by
    rw [hmul]; linarith
  have hle3 : 1 + Real.log (L : ℝ) ≤ 2 * Real.log (2 * (L : ℝ)) := by
    rw [hmul]; linarith
  -- Step 1: pull out the common factor `(1 + log L)³` from the sum.
  have hstep1 :
      (∑ n ∈ Finset.Icc 1 L,
          ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹)
        ≤ (1 + Real.log (L : ℝ)) ^ 3 *
            (∑ n ∈ Finset.Icc 1 L, ((Nat.divisors n).card : ℝ) ^ 2 * ((n : ℝ))⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨hn1, hn2⟩ := hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnR : (n : ℝ) ≤ (L : ℝ) := by exact_mod_cast hn2
    have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hlogn_le : Real.log (n : ℝ) ≤ Real.log (L : ℝ) := Real.log_le_log hnpos hnR
    have hnn : (0 : ℝ) ≤ ((Nat.divisors n).card : ℝ) ^ 2 * ((n : ℝ))⁻¹ :=
      mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hnpos))
    have hpow : (1 + Real.log (n : ℝ)) ^ 3 ≤ (1 + Real.log (L : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    calc ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹
        = ((Nat.divisors n).card : ℝ) ^ 2 * ((n : ℝ))⁻¹ * (1 + Real.log (n : ℝ)) ^ 3 := by
          ring
      _ ≤ ((Nat.divisors n).card : ℝ) ^ 2 * ((n : ℝ))⁻¹ * (1 + Real.log (L : ℝ)) ^ 3 :=
          mul_le_mul_of_nonneg_left hpow hnn
      _ = (1 + Real.log (L : ℝ)) ^ 3 *
            (((Nat.divisors n).card : ℝ) ^ 2 * ((n : ℝ))⁻¹) := by ring
  -- Step 2: apply the weighted second-moment bound.
  have heq :
      (∑ n ∈ Finset.Icc 1 L, ((Nat.divisors n).card : ℝ) ^ 2 * ((n : ℝ))⁻¹)
        = ∑ n ∈ Finset.Icc 1 L, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [div_eq_mul_inv]
  have hstep2 :
      (∑ n ∈ Finset.Icc 1 L, ((Nat.divisors n).card : ℝ) ^ 2 * ((n : ℝ))⁻¹)
        ≤ C₀ * (Real.log (2 * (L : ℝ))) ^ 4 := by
    rw [heq]; exact hC₀ L hL
  -- Step 3: `(1 + log L)³ ≤ 8 (log 2L)³` and combine.
  have hpow3 : (1 + Real.log (L : ℝ)) ^ 3 ≤ 8 * (Real.log (2 * (L : ℝ))) ^ 3 := by
    have := pow_le_pow_left₀ hbase hle3 3
    calc (1 + Real.log (L : ℝ)) ^ 3 ≤ (2 * Real.log (2 * (L : ℝ))) ^ 3 := this
      _ = 8 * (Real.log (2 * (L : ℝ))) ^ 3 := by ring
  have hC0log : (0 : ℝ) ≤ C₀ * (Real.log (2 * (L : ℝ))) ^ 4 :=
    mul_nonneg (le_of_lt hC₀pos) (by positivity)
  calc (∑ n ∈ Finset.Icc 1 L,
          ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹)
      ≤ (1 + Real.log (L : ℝ)) ^ 3 *
          (∑ n ∈ Finset.Icc 1 L, ((Nat.divisors n).card : ℝ) ^ 2 * ((n : ℝ))⁻¹) := hstep1
    _ ≤ (1 + Real.log (L : ℝ)) ^ 3 * (C₀ * (Real.log (2 * (L : ℝ))) ^ 4) :=
        mul_le_mul_of_nonneg_left hstep2 (pow_nonneg hbase 3)
    _ ≤ (8 * (Real.log (2 * (L : ℝ))) ^ 3) * (C₀ * (Real.log (2 * (L : ℝ))) ^ 4) :=
        mul_le_mul_of_nonneg_right hpow3 hC0log
    _ = 8 * C₀ * (Real.log (2 * (L : ℝ))) ^ 7 := by ring

end Work.ZeroDensity.Ingham
